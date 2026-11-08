-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.bodyTapes_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:07:57.060355+00:00
-- url     : https://prove2.me/submissions/98a32b80-87eb-46e4-9b72-f42b2482a8f3

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (C:List Bool) (S:P.K→List Bool) (k:P.K) (w:List Bool):
 Function.update (bodyTapes P C S) (.inl k) w=bodyTapes P C (Function.update S k w):=by
 funext j;cases j with
 |inl j=>by_cases hj:j=k <;>simp [bodyTapes,Function.update,hj]
 |inr j=>simp [bodyTapes,Function.update]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
