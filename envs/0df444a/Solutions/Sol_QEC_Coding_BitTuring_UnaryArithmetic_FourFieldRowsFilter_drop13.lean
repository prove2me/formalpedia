-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.drop13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:48.251203+00:00
-- url     : https://prove2.me/submissions/f33bf023-23fb-41a6-8295-1e9d9254cf98

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) :
 TM2.step (program P) (cfg P 13 f h I O H C B)=some (cfg P 14 f C.head? I O H C.tail B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
