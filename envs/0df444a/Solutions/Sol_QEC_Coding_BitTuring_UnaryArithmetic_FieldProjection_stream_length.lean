-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.stream_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:04.569199+00:00
-- url     : https://prove2.me/submissions/adb889cb-7bc2-4071-8e6a-aa79571adb75

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (xs:List ℕ) : (stream xs).length=xs.sum+xs.length := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>simp only [stream,List.length_append,unary_length,List.length_cons,
    ih,List.sum_cons];omega
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
