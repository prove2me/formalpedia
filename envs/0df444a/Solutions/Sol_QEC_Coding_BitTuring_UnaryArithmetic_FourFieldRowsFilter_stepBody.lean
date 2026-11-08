-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.stepBody
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:09:44.916467+00:00
-- url     : https://prove2.me/submissions/04d16d2c-6dad-4d49-85d9-50bfe380e811

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_stepAuxBody

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (C:List Bool) (c c':P.Cfg) (h:TM2.step P.program c=some c'):
 TM2.step (machine P).program (embedBody P C c)=some (embedBody P C c'):=by
 rcases c with ⟨l,v,S⟩;cases l with
 |none=>simp [TM2.step] at h
 |some l=>
  have hh:TM2.stepAux (P.program l) v S=c':=Option.some.inj h
  rw [←hh];exact congrArg some (stepAuxBody P C l v S)
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
