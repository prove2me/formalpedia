-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:21.689021+00:00
-- url     : https://prove2.me/submissions/966616ed-4b75-4ec1-bfee-c3227a45eb4a

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool)
 (I O H C B:List Bool):
 TM2.step (program P) (cfg P ⟨5+k.val,by omega⟩ f h I (true::O) H C B)=
 some (cfg P ⟨5+k.val,by omega⟩ f (some true) I O H (if f then C else true::C) B):=by
 fin_cases k <;> cases f
 all_goals simp [TM2.step,program,cfg,setHead,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 all_goals funext j;cases j with
 |inl j=>by_cases hi:j=P.input <;>by_cases ho:j=P.output <;>simp_all [Function.update,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
