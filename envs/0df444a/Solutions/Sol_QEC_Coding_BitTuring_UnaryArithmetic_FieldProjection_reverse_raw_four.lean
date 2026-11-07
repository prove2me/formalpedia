-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.reverse_raw_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:11.374208+00:00
-- url     : https://prove2.me/submissions/f10ace60-0763-4265-8f17-4e85ca66630e

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_four

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (a b c d:ℕ) : (raw [a,b,c,d]).reverse=raw [d,c,b,a] := by
  simp [raw_four,List.reverse_append,List.reverse_cons,unary,List.append_assoc]
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
