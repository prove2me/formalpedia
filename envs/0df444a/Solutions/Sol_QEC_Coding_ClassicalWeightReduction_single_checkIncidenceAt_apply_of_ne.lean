-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:43.721818+00:00
-- url     : https://prove2.me/submissions/306e45c5-389a-42e3-98f2-03e4c669d6b4

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution {c : Check} (e : Incidence R)
    (hc : e.1.1 ≠ c) (k : Fin (Fintype.card (CheckNeighbor R c))) :
    (Pi.single (Sum.inl (checkIncidenceAt R c k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) = 0 := by
  classical
  have he : checkIncidenceAt R c k ≠ e := by
    intro h
    apply hc
    have hv := congrArg (fun x : Incidence R => x.1.1) h
    simpa [checkIncidenceAt] using hv.symm
  simp [he]
end QEC.Coding.ClassicalWeightReduction
