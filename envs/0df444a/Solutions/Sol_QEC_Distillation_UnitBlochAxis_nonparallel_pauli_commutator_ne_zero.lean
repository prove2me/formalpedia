-- Prove2me | solution 1 for QEC.Distillation.UnitBlochAxis.nonparallel_pauli_commutator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:18:31.718431+00:00
-- url     : https://prove2.me/submissions/9f8f36c0-85cc-4243-b8ae-d6d428a45a67

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_UnitBlochAxis_nonparallel_crossSq_ne_zero
import Theorems.Thm_QEC_Distillation_blochPauliMatrix_commutator
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
namespace UnitBlochAxis
theorem _root_.solution
    {axis axis' : UnitBlochAxis} (h : axis.Nonparallel axis') :
    axisPauliMatrix axis * axisPauliMatrix axis' -
        axisPauliMatrix axis' * axisPauliMatrix axis ≠ 0 := by
  intro hzero
  have hcomm := blochPauliMatrix_commutator (blochVector axis) (blochVector axis')
  rw [blochPauliMatrix_blochVector, blochPauliMatrix_blochVector, hzero] at hcomm
  have hscalar : (2 : Complex) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hpauli : blochPauliMatrix (blochVector axis ⨯₃ blochVector axis') = 0 := by
    apply smul_right_injective SingleQubitMatrix hscalar
    simpa using hcomm.symm
  have hcross : blochVector axis ⨯₃ blochVector axis' = 0 := by
    have h2 : (blochVector axis ⨯₃ blochVector axis') 2 = 0 := by
      simpa [blochPauliMatrix] using congrFun (congrFun hpauli 0) 0
    have h01 := congrFun (congrFun hpauli 0) 1
    have h0 : (blochVector axis ⨯₃ blochVector axis') 0 = 0 := by
      have hre := congrArg Complex.re h01
      simpa [blochPauliMatrix, Complex.mul_re] using hre
    have h1 : (blochVector axis ⨯₃ blochVector axis') 1 = 0 := by
      have him := congrArg Complex.im h01
      have hneg : -(blochVector axis ⨯₃ blochVector axis') 1 = 0 := by
        simpa [blochPauliMatrix, Complex.mul_im] using him
      exact neg_eq_zero.mp hneg
    ext i
    fin_cases i <;> assumption
  have hsq : blochCrossSq axis axis' = 0 := by
    rw [show blochCrossSq axis axis' =
      (blochVector axis ⨯₃ blochVector axis') 0 ^ 2 +
        (blochVector axis ⨯₃ blochVector axis') 1 ^ 2 +
        (blochVector axis ⨯₃ blochVector axis') 2 ^ 2 by
      simp [blochCrossSq, blochVector, cross_apply]]
    simp [hcross]
  exact UnitBlochAxis.nonparallel_crossSq_ne_zero h hsq
end UnitBlochAxis
end QEC.Distillation
