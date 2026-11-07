-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.raw_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:27.330203+00:00
-- url     : https://prove2.me/submissions/c380de14-f6a8-4719-a36d-9d135af06174

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution (a b c d:ℕ) : raw [a,b,c,d]=
    unary a++false::(unary b++false::(unary c++false::unary d)) := by
  simpa [stream,List.append_assoc] using raw_append_last [a,b,c] d
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
