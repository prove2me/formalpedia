-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.restore11_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:10:34.443892+00:00
-- url     : https://prove2.me/submissions/6b9cad10-10d8-4d0e-8df8-76ffa756e9c1

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool) (a:Bool):
 TM2.step (program P) (cfg P 11 f h I O (a::H) C B)=some (cfg P 11 f (some a) (a::I) O H C B):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,setHead,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>
  simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
