-- Prove2me | solution 1 for QEC.Distillation.exists_alternatingAxisWord_of_mem_positiveLocalTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:16:33.734892+00:00
-- url     : https://prove2.me/submissions/def5a960-dd31-4d34-9b9a-6bef8c866983

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_specialScalar_alternatingAxisWord
import Theorems.Thm_QEC_Distillation_specialVector_alternatingAxisWord
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseInverseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_phaseNormalize_matrix
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseInverseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.phaseNormalize_matrix
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
theorem _root_.solution
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis')
    (U : SingleQubitSpecialUnitary)
    (hscalar : 0 < specialScalar U)
    (htarget : specialVector U ∈
      (alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel).target) :
    ∃ p : Fin 3 → Real,
      alternatingAxisWord axis axis' (p 0) (p 1) (p 2) = U := by
  let H := alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel
  let p : Fin 3 → Real := H.symm (specialVector U)
  have hpSource : p ∈ H.source := by
    simpa [p] using H.symm.map_source htarget
  have hpSource' : p ∈
      (alternatingWordLocalHomeomorph axis axis' hnonparallel).source ∩
        alternatingWordPositiveSet axis axis' := by
    simpa [H, alternatingWordPositiveLocalHomeomorph,
      OpenPartialHomeomorph.restrOpen_source] using hpSource
  have hpMap : alternatingWordMap axis axis' p = specialVector U := by
    exact H.right_inv htarget
  let W := alternatingAxisWord axis axis' (p 0) (p 1) (p 2)
  have hscalarW : 0 < specialScalar W := by
    rw [specialScalar_alternatingAxisWord]
    simpa [alternatingWordPositiveSet] using hpSource'.2
  have hvectorW : specialVector W = alternatingWordMap axis axis' p := by
    simpa [W, alternatingWordMap] using
      (specialVector_alternatingAxisWord axis axis' (p 0) (p 1) (p 2))
  have hvector : specialVector U = specialVector W := by
    rw [hvectorW, hpMap]
  have hnormU := special_coordinate_norm U
  have hnormW := special_coordinate_norm W
  have hsquares : specialScalar U ^ 2 = specialScalar W ^ 2 := by
    rw [hvector] at hnormU
    linarith
  have hsum : 0 < specialScalar U + specialScalar W := add_pos hscalar hscalarW
  have hproduct :
      (specialScalar U - specialScalar W) *
        (specialScalar U + specialScalar W) = 0 := by
    nlinarith [hsquares]
  have hscalarEq : specialScalar U = specialScalar W :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hsum))
  refine ⟨p, ?_⟩
  change W = U
  apply Subtype.ext
  apply Subtype.ext
  change (W : SingleQubitMatrix) = (U : SingleQubitMatrix)
  rw [special_coordinate_matrix W, special_coordinate_matrix U, hscalarEq, hvector]
end QEC.Distillation
