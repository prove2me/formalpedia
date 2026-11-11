-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTEvenOutput_global_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:12:47.383486+00:00
-- url     : https://prove2.me/submissions/5cbd7e82-036b-43ce-b8e9-76aef5ef9060

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_pi_div_four
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_neg_pi_div_six
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct
private theorem sourceTCos_sq_complex :
    (sourceTCos : Complex) * sourceTCos =
      ((1 + sourceTParameter) / 2 : Real) := by
  have h : sourceTCos * sourceTCos = (1 + sourceTParameter) / 2 := by
    simpa [pow_two] using sourceTCos_sq
  exact_mod_cast h
private theorem sourceTSin_sq_complex :
    (sourceTSin : Complex) * sourceTSin =
      ((1 - sourceTParameter) / 2 : Real) := by
  have h : sourceTSin * sourceTSin = (1 - sourceTParameter) / 2 := by
    simpa [pow_two] using sourceTSin_sq
  exact_mod_cast h
private theorem sourceTEvenFirstQubit_apply_zero :
    sourceTEvenFirstQubit 0 =
      (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
        (sourceTCos : Complex) * sourceTCos := by
  simp [sourceTEvenFirstQubit, zzEvenBranchFirstQubit, zzEvenBranchState,
    sourceTEvenWeight, zzEvenProjector_sourceTTwoQubitState_apply] <;> ring
private theorem phaseAmplitude_pi_div_four_sq :
    phaseAmplitude (Real.pi / 4) * phaseAmplitude (Real.pi / 4) = Complex.I := by
  rw [phaseAmplitude_pi_div_four]
  have hsqrt : (Real.sqrt 2 : Complex) * Real.sqrt 2 = 2 := by
    exact_mod_cast sqrt_two_mul_self
  rw [show (Real.sqrt 2 / 2 : Complex) = Real.sqrt 2 * (2 : Complex)⁻¹ by ring]
  ring_nf
  rw [Complex.I_sq]
  field_simp
  rw [pow_two, hsqrt]
  ring
private theorem sourceTEvenFirstQubit_apply_one :
    sourceTEvenFirstQubit 1 =
      (Real.sqrt sourceTEvenWeight : Complex)⁻¹ * Complex.I *
        (sourceTSin : Complex) * sourceTSin := by
  simp only [sourceTEvenFirstQubit, zzEvenBranchFirstQubit, zzEvenBranchState]
  change (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
      zzEvenProjector sourceTTwoQubitState
        (pairBitstring (1, controlledXBit 1 0)) = _
  have hprojected : zzEvenProjector sourceTTwoQubitState
      (pairBitstring (1, 1)) =
      (phaseAmplitude (Real.pi / 4) * sourceTSin) *
        (phaseAmplitude (Real.pi / 4) * sourceTSin) := by
    simpa only [sourceTState_apply_one, if_pos rfl, if_true] using
      (zzEvenProjector_sourceTTwoQubitState_apply 1 1)
  rw [controlledXBit_one, flipBit_zero]
  rw [hprojected]
  calc
    _ = (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
        (phaseAmplitude (Real.pi / 4) * phaseAmplitude (Real.pi / 4)) *
          sourceTSin * sourceTSin := by ring
    _ = _ := by rw [phaseAmplitude_pi_div_four_sq]
private theorem sourceTEvenFirstQubit_phase_ratio :
    (hadamardOperator sourceTEvenFirstQubit) 1 =
      phaseAmplitude (-Real.pi / 6) *
        (hadamardOperator sourceTEvenFirstQubit) 0 := by
  rw [hadamardOperator_apply_one, hadamardOperator_apply_zero,
    sourceTEvenFirstQubit_apply_zero, sourceTEvenFirstQubit_apply_one,
    phaseAmplitude_neg_pi_div_six]
  have hweight_ne : (Real.sqrt sourceTEvenWeight : Complex) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 sourceTEvenWeight_pos).ne'
  have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  field_simp [hweight_ne, hsqrt_two_ne, sqrt_three_ne_zero]
  push_cast
  ring_nf
  have hcos : (sourceTCos : Complex) ^ 2 =
      ((1 + sourceTParameter) / 2 : Real) := by
    simpa [pow_two] using sourceTCos_sq_complex
  have hsin : (sourceTSin : Complex) ^ 2 =
      ((1 - sourceTParameter) / 2 : Real) := by
    simpa [pow_two] using sourceTSin_sq_complex
  rw [hcos, hsin]
  ring_nf
  norm_num [sourceTParameter]
  have hsqrt_three_ne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_three_ne_zero
  field_simp [hsqrt_three_ne]
  have hsqrt_three_sq : (Real.sqrt 3 : Complex) ^ 2 = 3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3))
  ring_nf
  rw [hsqrt_three_sq]
  ring
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
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    hadamardOperator sourceTEvenFirstQubit =
      sourceTGlobalPhase • phaseState (-Real.pi / 6) := by
  ext b
  fin_cases b
  · change (hadamardOperator sourceTEvenFirstQubit) 0 =
      sourceTGlobalPhase * phaseState (-Real.pi / 6) 0
    rw [phaseState_apply_zero, sourceTGlobalPhase]
    have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    field_simp [hsqrt_two_ne]
  · change (hadamardOperator sourceTEvenFirstQubit) 1 =
      sourceTGlobalPhase * phaseState (-Real.pi / 6) 1
    rw [phaseState_apply_one, sourceTGlobalPhase,
      sourceTEvenFirstQubit_phase_ratio]
    have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    field_simp [hsqrt_two_ne]
end QEC.Distillation.OneQubitMagic
