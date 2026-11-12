-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hAngleWord_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:06:01.54566+00:00
-- url     : https://prove2.me/submissions/a2a2b2ef-7831-40ec-95af-313a098ff116

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_neg_pi_div_four
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open GeneratedUniversality
private theorem hAngleSqrtTwoNeZeroComplex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_two_pos.ne'
private theorem hAngleSqrtTwoMulSelfComplex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self
@[simp] private theorem complex_I_pow_two : Complex.I ^ 2 = -1 :=
  Complex.I_sq
@[simp] private theorem complex_I_pow_three : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, complex_I_pow_two]
  ring
@[simp] private theorem complex_I_pow_four : Complex.I ^ 4 = 1 := by
  rw [pow_succ, complex_I_pow_three]
  ring_nf
  rw [Complex.I_sq]
  norm_num
@[simp] private theorem complex_I_pow_five : Complex.I ^ 5 = Complex.I := by
  rw [pow_succ, complex_I_pow_four, one_mul]
@[simp] private theorem complex_I_pow_six : Complex.I ^ 6 = -1 := by
  rw [pow_succ, complex_I_pow_five, Complex.I_mul_I]
@[simp] private theorem complex_I_pow_seven : Complex.I ^ 7 = -Complex.I := by
  rw [pow_succ, complex_I_pow_six]
  ring
@[simp] private theorem complex_I_pow_eight : Complex.I ^ 8 = 1 := by
  rw [pow_succ, complex_I_pow_seven]
  ring_nf
  rw [Complex.I_sq]
  norm_num
@[simp] private theorem sqrt_two_pow_two_complex :
    (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  simpa [pow_two] using hAngleSqrtTwoMulSelfComplex
@[simp] private theorem sqrt_two_pow_three_complex :
    (Real.sqrt 2 : Complex) ^ 3 = 2 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_two_complex]
@[simp] private theorem sqrt_two_pow_four_complex :
    (Real.sqrt 2 : Complex) ^ 4 = 4 := by
  rw [pow_succ, sqrt_two_pow_three_complex]
  calc
    2 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        2 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 4 := by rw [hAngleSqrtTwoMulSelfComplex]; norm_num
@[simp] private theorem sqrt_two_pow_five_complex :
    (Real.sqrt 2 : Complex) ^ 5 = 4 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_four_complex]
@[simp] private theorem sqrt_two_pow_six_complex :
    (Real.sqrt 2 : Complex) ^ 6 = 8 := by
  rw [pow_succ, sqrt_two_pow_five_complex]
  calc
    4 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        4 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 8 := by rw [hAngleSqrtTwoMulSelfComplex]; norm_num
@[simp] private theorem sqrt_two_pow_seven_complex :
    (Real.sqrt 2 : Complex) ^ 7 = 8 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_six_complex]
@[simp] private theorem sqrt_two_pow_eight_complex :
    (Real.sqrt 2 : Complex) ^ 8 = 16 := by
  rw [pow_succ, sqrt_two_pow_seven_complex]
  calc
    8 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        8 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 16 := by rw [hAngleSqrtTwoMulSelfComplex]; norm_num
end OneQubitMagic
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    (hAngleWord : SingleQubitMatrix) =
      !![(3 : Complex) / 4 + Complex.I * ((Real.sqrt 2 - 1 : Real) / 4),
         -(1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4);
         (1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4),
         (3 : Complex) / 4 + Complex.I * ((1 - Real.sqrt 2 : Real) / 4)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hAngleWord, hadamardGate, phaseGate, phaseShiftGate,
      hadamardMatrix, phaseMatrix, phaseShiftMatrix,
      phaseAmplitude_neg_pi_div_four, pow_succ]
  all_goals
    field_simp [hAngleSqrtTwoNeZeroComplex]
    ring_nf
    simp only [complex_I_pow_two, complex_I_pow_three, complex_I_pow_four,
      complex_I_pow_five, complex_I_pow_six, complex_I_pow_seven,
      complex_I_pow_eight, sqrt_two_pow_two_complex, sqrt_two_pow_three_complex,
      sqrt_two_pow_six_complex, sqrt_two_pow_seven_complex, sqrt_two_pow_eight_complex]
    ring
end QEC.Distillation.OneQubitMagic
