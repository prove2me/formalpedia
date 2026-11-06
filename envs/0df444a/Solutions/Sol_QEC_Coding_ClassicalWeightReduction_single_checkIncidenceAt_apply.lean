-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.single_checkIncidenceAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:39.725657+00:00
-- url     : https://prove2.me/submissions/9dab2f2c-33cc-481d-8953-bbbdcff316c8

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
theorem _root_.solution (e : Incidence R)
    (k : Fin (Fintype.card (CheckNeighbor R e.1.1))) :
    (Pi.single (Sum.inl (checkIncidenceAt R e.1.1 k)) 1 :
        Word F (WeightReducedCheck R)) (Sum.inl e) =
      (Pi.single k 1 : Word F
        (Fin (Fintype.card (CheckNeighbor R e.1.1)))) (checkPosition R e) := by
  classical
  by_cases hk : k = checkPosition R e
  · subst k
    rw [checkIncidenceAt_checkPosition R e]
    simp
  · have he : checkIncidenceAt R e.1.1 k ≠ e := by
      intro h
      apply hk
      have hn : checkNeighborOrder R e.1.1 k = ⟨e.1.2, e.2⟩ := by
        apply Subtype.ext
        exact congrArg (fun x : Incidence R => x.1.2) h
      have hp := congrArg (checkNeighborOrder R e.1.1).symm hn
      simpa [checkPosition] using hp
    simp [hk, he]
end QEC.Coding.ClassicalWeightReduction
