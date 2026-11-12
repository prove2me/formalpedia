-- Prove2me | solution 1 for QEC.Distillation.specialVector_alternatingAxisWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:05:21.672163+00:00
-- url     : https://prove2.me/submissions/0e6b3653-3598-4357-a925-29e6414b1856

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_alternatingAxisWord_matrix
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
theorem _root_.solution (axis axis' : UnitBlochAxis) (x y z : Real) :
    specialVector (alternatingAxisWord axis axis' x y z) =
      alternatingWordVector axis axis' x y z := by
  ext i
  fin_cases i <;>
    simp only [specialVector, Matrix.vecEmpty, Fin.isValue]
  all_goals
    rw [alternatingAxisWord_matrix]
    simp [su2Matrix, blochPauliMatrix]
end QEC.Distillation
