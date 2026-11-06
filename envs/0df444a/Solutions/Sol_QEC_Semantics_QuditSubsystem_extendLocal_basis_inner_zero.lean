-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_basis_inner_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:15.796301+00:00
-- url     : https://prove2.me/submissions/f18d3130-63f1-4e7a-a3c0-22f92ebb0e0c

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_basis_inner
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators TensorProduct
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) (h : ∃ j, j ∉ S.selected ∧ x j ≠ y j) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) = 0 := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hcomp : (S.splitLabel x).2 ≠ (S.splitLabel y).2 := by
    intro heq
    exact hxy (congrFun heq ⟨j, hj⟩)
  rw [extendLocal_basis_inner]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, hcomp]
end QEC.Semantics.QuditSubsystem
