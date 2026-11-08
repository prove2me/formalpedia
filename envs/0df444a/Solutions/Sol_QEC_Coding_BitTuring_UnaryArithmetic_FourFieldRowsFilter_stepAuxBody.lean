-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.stepAuxBody
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:08:49.908517+00:00
-- url     : https://prove2.me/submissions/51adf517-6420-4635-8aea-fe31978db9c1

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_bodyTapes_update

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring Turing StateTransition
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (C:List Bool) (l:P.Λ) (v:P.σ) (S:P.K→List Bool):
 TM2.stepAux (program P (.inl l)) (v,false,none) (bodyTapes P C S)=
 embedBody P C (TM2.stepAux (P.program l) v S):=
 stepAux_liftStatement (K:=P.K) (K':=Stack P) (Λ:=P.Λ) (Λ':=Label P)
  (σ:=P.σ) (σ':=Var P) Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
  (some (.inr 3)) (fun v=>(v,false,none)) (bodyTapes P C)
  (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (bodyTapes_update P C) (P.program l) v S
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
