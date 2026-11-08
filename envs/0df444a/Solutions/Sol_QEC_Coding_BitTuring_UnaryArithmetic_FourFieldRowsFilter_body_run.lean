-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.body_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:08.489194+00:00
-- url     : https://prove2.me/submissions/c272c53a-3bf4-4019-8cee-3cd4ebbe39ef

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_stepBody

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (C x y:List Bool) (n:ℕ)
 (hn:(fun c=>c.bind (TM2.step P.program))^[n] (some (P.init x))=some (P.halt y)):
 (next P)^[n] (some (embedBody P C (P.init x)))=some (embedBody P C (P.halt y)):=
 iterate_lift (TM2.step P.program) (TM2.step (program P)) (embedBody P C)
  (stepBody P C) n _ _ hn
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
