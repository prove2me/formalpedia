-- Prove2me | solution 1 for QEC.Semantics.FiniteAlphabet.localOperator_basis_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:15:40.735203+00:00
-- url     : https://prove2.me/submissions/ef662c33-3133-434f-80d5-f45aafb7b7db

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_inner
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
attribute [local instance] QEC.Semantics.FiniteAlphabet._p2m_local_instance_ac378d2a8a_23
variable {A I}
namespace QEC.Semantics.FiniteAlphabet
theorem _root_.solution
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (x y : I → A) (h : ∃ j, j ∉ S.selected ∧ x j ≠ y j) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) = 0 := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hcomp : (S.splitLabel (labelEquiv A I x)).2 ≠
      (S.splitLabel (labelEquiv A I y)).2 := by
    intro heq
    have hv := congrFun heq ⟨j, hj⟩
    exact hxy ((Fintype.equivFin A).injective hv)
  rw [localOperator_basis_inner]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, hcomp]
end QEC.Semantics.FiniteAlphabet
