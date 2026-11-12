-- Prove2me | solution 1 for QEC.Distillation.subgroup_isOpen_of_contains_nonparallel_axisCircles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:23:30.238209+00:00
-- url     : https://prove2.me/submissions/34452b35-0228-4117-92b3-625433d76c13

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_alternatingAxisWord_mem
import Theorems.Thm_QEC_Distillation_continuous_specialScalar
import Theorems.Thm_QEC_Distillation_continuous_specialVector
import Theorems.Thm_QEC_Distillation_specialScalar_alternatingAxisWord
import Theorems.Thm_QEC_Distillation_specialVector_alternatingAxisWord
import Theorems.Thm_QEC_Distillation_alternatingWordBase_mem_positiveSet
import Theorems.Thm_QEC_Distillation_alternatingWordBase_mem_positiveLocalHomeomorph_source
import Theorems.Thm_QEC_Distillation_exists_alternatingAxisWord_of_mem_positiveLocalTarget
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
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    IsOpen (K : Set SingleQubitSpecialUnitary) := by
  let H := alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel
  let V : Set SingleQubitSpecialUnitary :=
    {U | 0 < specialScalar U ∧ specialVector U ∈ H.target}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const continuous_specialScalar).inter
      (continuous_specialVector.isOpen_preimage H.target H.open_target)
  let W := alternatingAxisWord axis axis' 0 (Real.pi / 4) 0
  have hbaseSource : alternatingWordBase ∈ H.source := by
    simpa [H] using
      (alternatingWordBase_mem_positiveLocalHomeomorph_source axis axis' hnonparallel)
  have hbaseTarget : alternatingWordMap axis axis' alternatingWordBase ∈ H.target :=
    H.map_source hbaseSource
  have hWscalar : 0 < specialScalar W := by
    rw [specialScalar_alternatingAxisWord]
    exact alternatingWordBase_mem_positiveSet axis axis'
  have hWvector : specialVector W =
      alternatingWordMap axis axis' alternatingWordBase := by
    exact specialVector_alternatingAxisWord axis axis' 0 (Real.pi / 4) 0
  have hWV : W ∈ V := ⟨hWscalar, by simpa [hWvector] using hbaseTarget⟩
  have hVK : V ⊆ K := by
    intro U hU
    obtain ⟨p, hp⟩ :=
      exists_alternatingAxisWord_of_mem_positiveLocalTarget axis axis' hnonparallel U hU.1 hU.2
    rw [← hp]
    exact alternatingAxisWord_mem K axis axis' haxis haxis' (p 0) (p 1) (p 2)
  apply Subgroup.isOpen_of_mem_nhds K
  exact Filter.mem_of_superset (hVopen.mem_nhds hWV) hVK
end QEC.Distillation
