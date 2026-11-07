-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.fields_stream_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:11.573002+00:00
-- url     : https://prove2.me/submissions/6f3970b1-a507-4f6d-af16-54bd8591b5d3

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (i:ℕ) (xs:List ℕ) :
    (stream (fields n keep i xs)).length≤(stream xs).length := by
  have h:=buffer_length_le n keep i xs []
  rw [buffer_eq] at h
  simpa only [List.append_nil,List.length_reverse,List.length_nil,Nat.add_zero] using h
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
