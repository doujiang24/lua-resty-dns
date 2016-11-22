local req_sock = ngx.req.udp_socket
local bit = require "bit"
local byte = string.byte
local lshift = bit.lshift
local rshift = bit.rshift
local concat = table.concat
local char = string.char
local band = bit.band
local sub = string.sub
local gsub = string.gsub
local re_find = ngx.re.find
local str_lower = string.lower
local clear_tb = require "table.clear"
local new_tab = require "table.new"
local split = require "ngx.re" .split

local TYPE_A      = 1
local TYPE_NS     = 2
local TYPE_CNAME  = 5
local TYPE_SOA    = 6
local TYPE_PTR    = 12
local TYPE_MX     = 15
local TYPE_TXT    = 16
local TYPE_AAAA   = 28
local TYPE_SRV    = 33
local TYPE_SPF    = 99

local CLASS_IN    = 1

local labels = {}
local address_segs = {}
local AN_SECTION, NS_SECTION, AR_SECTION, response = {}, {}, {}, {}


local _M = {
    _VERSION    = '0.01',
    TYPE_A      = TYPE_A,
    TYPE_NS     = TYPE_NS,
    TYPE_CNAME  = TYPE_CNAME,
    TYPE_SOA    = TYPE_SOA,
    TYPE_PTR    = TYPE_PTR,
    TYPE_MX     = TYPE_MX,
    TYPE_TXT    = TYPE_TXT,
    TYPE_AAAA   = TYPE_AAAA,
    TYPE_SRV    = TYPE_SRV,
    TYPE_SPF    = TYPE_SPF,
    CLASS_IN    = CLASS_IN,
}
local mt = { __index = _M }


local function _decode_name(buf, pos)
    clear_tb(labels)

    local idx = 0
    local nptrs = 0
    local p = pos
    while nptrs < 128 do
        local fst = byte(buf, p)

        if not fst then
            return nil, "truncated"
        end

        -- print("fst at ", p, ": ", fst)

        if fst == 0 then
            if nptrs == 0 then
                pos = pos + 1
            end
            break
        end

        if band(fst, 0xc0) ~= 0 then
            -- being a pointer
            if nptrs == 0 then
                pos = pos + 2
            end

            nptrs = nptrs + 1

            local snd = byte(buf, p + 1)
            if not snd then
                return nil, "truncated"
            end

            p = lshift(band(fst, 0x3f), 8) + snd + 1

            -- print("resolving ptr ", p, ": ", byte(buf, p))

        else
            -- being a label
            local label = sub(buf, p + 1, p + fst)
            idx = idx + 1
            labels[idx] = label

            -- print("resolved label ", label)

            p = p + fst + 1

            if nptrs == 0 then
                pos = p
            end
        end
    end

    return concat(labels, "."), pos
end


function _M.new(self, opts)
    local sock, err = req_sock(true)
    if not sock then
        return nil, err
    end

    return setmetatable({
        sock = sock,
        flag_AA = opts and opts.flag_AA or 0,
        flag_RA = opts and opts.flag_RA or 0,
    }, mt)
end


function _M.receive(self)
    local sock = self.sock

    local req, err = sock:receive()
    if not req then
        return nil, err
    end

    local n = #req
    if n < 12 then
        return nil, "truncated"
    end

    local ident_hi, ident_lo = byte(req, 1, 2)
    local id = lshift(ident_hi, 8) + ident_lo

    local flags_hi, flags_lo = byte(req, 3, 4)
    local flags = lshift(flags_hi, 8) + flags_lo

    if band(flags, 0x8000) == 1 then
        return nil, "bad QR flag in the DNS request"
    end

    local flag_RD = band(rshift(flags, 8), 0x1)

    -- local code = band(flags, 0xf)

    local nqs_hi, nqs_lo = byte(req, 5, 6)
    local nqs = lshift(nqs_hi, 8) + nqs_lo

    if nqs ~= 1 then
        return nil, "only one question supported, but seen: " .. nqs
    end

    local qname, pos = _decode_name(req, 13)
    if not qname then
        return nil, "bad question"
    end

    if re_find(qname, "[A-Z]", "jo") then
        qname = str_lower(qname)
    end

    -- print("question qname: ", qname)

    local typ_hi, typ_lo = byte(req, pos, pos + 1)
    local typ = lshift(typ_hi, 8) + typ_lo

    local class_hi, class_lo = byte(req, pos + 2, pos + 3)
    local class = lshift(class_hi, 8) + class_lo

    self.id = id
    self.flag_RD = flag_RD
    self.raw_question_rr = sub(req, 13, pos + 3)

    return qname, typ, class
end


local function _encode_label(label)
    return char(#label) .. label
end


local function _encode_name(name)
    return gsub(name, "([^.]+)%.?", _encode_label) .. '\0'
end


local function _int16(int)
    return char(rshift(int, 8), band(int, 0xFF))
end


local function _int32(int)
    return char(band(rshift(int, 24), 0xFF),
                band(rshift(int, 16), 0xFF),
                band(rshift(int, 8), 0xFF),
                band(int, 0xFF))
end


local function _build_section(answers, n, section)
    clear_tb(section)

    for i = 1, n do
        local ans = answers[i]
        local typ = ans.type or TYPE_A
        local class = ans.class or CLASS_IN
        local ttl = ans.ttl or 0

        local len, data

        if typ == TYPE_A then
            address_segs = split(ans.address, [[\.]], "jo", nil, 4, address_segs)
            data = char(tonumber(address_segs[1]),
                        tonumber(address_segs[2]),
                        tonumber(address_segs[3]),
                        tonumber(address_segs[4]))

            len = #data

        elseif typ == TYPE_CNAME then
            data = _encode_name(ans.cname)
            len = #data

        elseif typ == TYPE_NS then
            data = _encode_name(ans.nsdname)
            len = #data

        else
            return nil, "not supported type: " .. typ
        end

        local pos = i * 6

        section[pos - 5] = _encode_name(ans.name)
        section[pos - 4] = _int16(typ)
        section[pos - 3] = _int16(class)
        section[pos - 2] = _int32(ttl)
        section[pos - 1] = _int16(len)
        section[pos] = data
    end

    return section
end


function _M.answer(self, answers, nameservers, additionals, opts)
    local id = self.id
    if not id then
        return nil, "no question received"
    end

    local nqs = 1
    local nan = #answers
    local nns = nameservers and #nameservers or 0
    local nar = additionals and #additionals or 0

    local an_section, err = _build_section(answers, nan, AN_SECTION)
    if not an_section then
        return nil, err
    end

    local ns_section, ar_section

    if nameservers then
        ns_section, err = _build_section(nameservers, nns, NS_SECTION)
        if not ns_section then
            return nil, err
        end
    end

    if additionals then
        ar_section, err = _build_section(additionals, nar, AR_SECTION)
        if not ar_section then
            return nil, err
        end
    end

    local flags = lshift(1, 15)
                  + lshift(self.flag_AA, 10)
                  + lshift(self.flag_RD, 8)
                  + lshift(self.flag_RA, 7)

    response[1] = _int16(id)
    response[2] = _int16(flags)
    response[3] = _int16(nqs)
    response[4] = _int16(nan)
    response[5] = _int16(nns)
    response[6] = _int16(nar)
    response[7] = self.raw_question_rr
    response[8] = an_section
    response[9] = ns_section or ""
    response[10] = ar_section or ""

    local ok
    ok, err = self.sock:send(response)
    if not ok then
        return nil, err
    end

    return true
end


return _M
