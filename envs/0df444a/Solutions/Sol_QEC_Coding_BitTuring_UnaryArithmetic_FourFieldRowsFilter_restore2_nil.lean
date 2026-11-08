-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.restore2_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:55.231042+00:00
-- url     : https://prove2.me/submissions/8282cc98-76af-4d30-bfe5-b91a2b67aab6

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I C:List Bool) :
 TM2.step (program P) (cfg P 2 f h I [] [] C [])=some (embedBody P C (P.init I)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,embedBody,liftCfg,Machine.init,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm,bodyTapes]
 |inr j=>fin_cases j <;>simp [Function.update,bodyTapes]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
