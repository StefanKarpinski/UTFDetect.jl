module UTFDetect

utf8_lead_1(b::UInt8) = leading_ones(b) == 0
utf8_lead_2(b::UInt8) = leading_ones(b) == 2
utf8_lead_3(b::UInt8) = leading_ones(b) == 3
utf8_lead_4(b::UInt8) = leading_ones(b) == 4
utf8_cont(b::UInt8)   = leading_ones(b) == 1

utf16_lone(b::UInt8)  = (b >> 3) != 0b11011
utf16_lead(b::UInt8)  = (b >> 2) == 0b110110
utf16_trail(b::UInt8) = (b >> 2) == 0b110111

utf32_byte_4(b::UInt8) = b == 0x00
utf32_byte_3(b::UInt8) = b <= 0x10

false_p(b::UInt8) = false
true_p(b::UInt8)  = true

const predicates = [
    utf8_lead_1, utf8_lead_2, utf8_lead_3, utf8_lead_4, utf8_cont,
    utf16_lone, utf16_lead, utf16_trail,
    utf32_byte_4, utf32_byte_3,
    false_p, true_p,
]

p_mask(byte::UInt8) =
    sum(pred(byte) << (i-1) for (i, pred) in enumerate(predicates))
p_mask(p::Vector{<:Function}) =
    sum((pred in p) << (i-1) for (i, pred) in enumerate(predicates))

p_masks = sort!(unique(p_mask(byte) for byte = 0x0:0xff))
# 10 total predicate masks < 4 bits
@assert length(p_masks) == 10

# construct a predicate lookup table indexing into p_masks
p_table = UInt8[findfirst(==(p_mask(UInt8(b))), p_masks)-1 for b=0x00:0xff]
@assert all(p_mask(b) == p_masks[p_table[b+1]+1] for b = 0x00:0xff)

# UTF-8 state: counter of remaining trailing bytes from 3 down to 0 (bits: 2)
# UTF-16 state: hi/lo alternator, trail indicator (bits: 3, one shared with UTF-32)
# UTF-32 state: byte counter for 0-3 (bits: 2, one shared with UTF-16)
# total state: 6 bits (3 data-dependent, 3 data-independent)

# preds: value from p_table, index into p_masks
# represents a possible set of true predicates

function ⋲(p::Function, preds::UInt8)
    mask = p_masks[preds+1]
    for (i, p′) in enumerate(predicates)
        p′ == p && return !iszero(mask & (1 << (i-1)))
    end
    error("predicate not found: $p")
end

# u8_next: u8_trail must be 0 at start of a character
# set to the number of trailing continuation characters
# decremented after each continuation character

function u8_next(preds::UInt8, u8_trail::UInt8)::UInt8
    utf8_cont   ⋲ preds ? max(0, u8_trail-1) :
    utf8_lead_4 ⋲ preds ? 3 :
    utf8_lead_3 ⋲ preds ? 2 :
    utf8_lead_2 ⋲ preds ? 1 : 0
end

function u8_valid(u8_trail::UInt8)
    u8_trail == 0 ?
        p_mask([utf8_lead_1, utf8_lead_2, utf8_lead_3, utf8_lead_4]) :
        p_mask([utf8_cont])
end

# u16_next: only called on high bytes, for little-endian & big-endian
# there's a separate state bit for each one that's passed through as-is
# for bytes that aren't the high byte for that endianness

function u16_next(preds::UInt8)::UInt8
    utf16_lead ⋲ preds
end

function u16_valid(u16_trail::UInt8, count::UInt8, be::Bool)
    hi = be ⊻ isodd(count) # count is zero-based
    hi && u16_trail == 0 ? p_mask([utf16_lone, utf16_lead]) :
    hi && u16_trail == 1 ? p_mask([utf16_trail]) :
                           p_mask([true_p])
end

# u32_next: doesn't exist since UTF-32 has no data-dependent state

function u32_valid(count::UInt8, be::Bool)
    (count & 3) == (be ? 0 : 3) ? p_mask([utf32_byte_4]) :
    (count & 3) == (be ? 1 : 2) ? p_mask([utf32_byte_3]) :
                                  p_mask([true_p])
end

# build the transition table

t_table = zeros(UInt8, 2^4*2^2*10)
indices = Int[]
for u8_trail = 0b00:0b11, u16l_trail = 0b0:0b1, u16b_trail = 0b0:0b1
    state = u8_trail | (u16l_trail << 2) | (u16b_trail << 3)
    for count = 0b00:0b11
        mask_u8   = u8_valid(u8_trail)
        mask_u16l = u16_valid(u16l_trail, count, false)
        mask_u16b = u16_valid(u16b_trail, count, true)
        mask_u32l = u32_valid(count, false)
        mask_u32b = u32_valid(count, true)
        for preds in 0x0:0x9
            index = state | (count << 4) | (UInt16(preds) << 6)
            # compute the valid mask
            mask  = p_masks[preds+1]
            u8    = UInt8(!iszero(mask & mask_u8))
            u16l  = UInt8(!iszero(mask & mask_u16l))
            u16b  = UInt8(!iszero(mask & mask_u16b))
            u32l  = UInt8(!iszero(mask & mask_u32l))
            u32b  = UInt8(!iszero(mask & mask_u32b))
            valid = u8 | (u16l << 1) | (u16b << 2) | (u32l << 3) | (u32b << 4)
            # compute the next state
            u8_trail′ = u8_next(preds, u8_trail)
            if iseven(count)
                u16l_trail′ = u16l_trail
                u16b_trail′ = u16_next(preds)
            else
                u16l_trail′ = u16_next(preds)
                u16b_trail′ = u16b_trail
            end
            state′ = u8_trail′ | (u16l_trail′ << 2) | (u16b_trail′ << 3)
            # populate the table
            t_table[index + 1] = valid | (state′ << 5)
            push!(indices, index)
        end
    end
end
@assert sort!(indices) == 0:length(t_table)-1

const table = Tuple([p_table; t_table])

function detect(bytes::Union{AbstractVector{UInt8}, IO})
    valid = 0b11111
    state = 0b000
    count = 0b00
    @inbounds for byte in bytes
        preds = table[byte + 1]
        index = state | (count << 4) | (UInt16(preds) << 6)
        state = table[index + 1 + 256]
        valid &= state
        state >>= 5
        count = (count + 0x1) & 0x3
    end
    return valid, state, count
end

end # module
