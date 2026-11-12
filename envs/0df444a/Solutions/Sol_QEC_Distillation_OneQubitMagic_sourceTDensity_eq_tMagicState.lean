-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTDensity_eq_tMagicState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:00:53.7232+00:00
-- url     : https://prove2.me/submissions/e2c05277-a4f0-473b-b977-cc6fe3017806

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTSin_mul_sourceTCos
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_pi_div_four
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
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
private theorem sourceTParameter_mul_sqrt_three :
    sourceTParameter * Real.sqrt 3 = 1 := by
  unfold sourceTParameter
  field_simp [sqrt_three_ne_zero]
private theorem sourceTParameter_complex_eq_inv_sqrt_three :
    (sourceTParameter : Complex) = (Real.sqrt 3 : Complex)⁻¹ := by
  have hsqrt_three_ne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_three_ne_zero
  have hparameter :
      (sourceTParameter : Complex) * (Real.sqrt 3 : Complex) = 1 := by
    exact_mod_cast sourceTParameter_mul_sqrt_three
  calc
    (sourceTParameter : Complex) =
        (sourceTParameter : Complex) * 1 := by ring
    _ = (sourceTParameter : Complex) *
        ((Real.sqrt 3 : Complex) * (Real.sqrt 3 : Complex)⁻¹) := by
      rw [mul_inv_cancel₀ hsqrt_three_ne, mul_one]
    _ = ((sourceTParameter : Complex) * (Real.sqrt 3 : Complex)) *
        (Real.sqrt 3 : Complex)⁻¹ := by ring
    _ = (Real.sqrt 3 : Complex)⁻¹ := by
      rw [hparameter, one_mul]
private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
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
private theorem sourceTState_scaled_cross :
    sourceTCos * sourceTSin * Real.sqrt 2 = sourceTParameter := by
  rw [show sourceTCos * sourceTSin = sourceTSin * sourceTCos by ring,
    sourceTSin_mul_sourceTCos]
  field_simp [sqrt_two_pos.ne']
private theorem sourceTState_upper_cross :
    (sourceTCos : Complex) *
        (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
      (sourceTParameter / 2 : Real) -
        (sourceTParameter / 2 : Real) * Complex.I := by
  have hphase : star (phaseAmplitude (Real.pi / 4)) =
      (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
    rw [phaseAmplitude_pi_div_four]
    push_cast
    simp
    ring
  have hscaled : (sourceTCos : Complex) * sourceTSin * Real.sqrt 2 =
      sourceTParameter := by
    exact_mod_cast sourceTState_scaled_cross
  rw [hphase]
  calc
    (sourceTCos : Complex) *
        (((Real.sqrt 2 / 2 : Complex) -
          (Real.sqrt 2 / 2 : Complex) * Complex.I) * sourceTSin) =
        ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 -
          ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 *
            Complex.I := by
      push_cast
      ring
    _ = (sourceTParameter / 2 : Real) -
          (sourceTParameter / 2 : Real) * Complex.I := by
      rw [hscaled]
      norm_num
private theorem sourceTState_lower_cross :
    phaseAmplitude (Real.pi / 4) * sourceTSin * sourceTCos =
      (sourceTParameter / 2 : Real) +
        (sourceTParameter / 2 : Real) * Complex.I := by
  have hscaled : (sourceTCos : Complex) * sourceTSin * Real.sqrt 2 =
      sourceTParameter := by
    exact_mod_cast sourceTState_scaled_cross
  rw [phaseAmplitude_pi_div_four]
  calc
    ((Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I) *
          sourceTSin * sourceTCos =
        ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 +
          ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 *
            Complex.I := by
      push_cast
      ring
    _ = (sourceTParameter / 2 : Real) +
          (sourceTParameter / 2 : Real) * Complex.I := by
      rw [hscaled]
      norm_num
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
theorem _root_.solution : sourceTDensity = tMagicState := by
  apply densityOperator_ext_toOperator
  rw [sourceTDensity_toOperator]
  change
    (InnerProductSpace.rankOne Complex sourceTState sourceTState).toLinearMap =
      blochProjector tBloch
  ext psi b
  fin_cases b
  · change
      ((InnerProductSpace.rankOne Complex sourceTState sourceTState) psi) 0 =
        (blochProjector tBloch psi) 0
    rw [InnerProductSpace.rankOne_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
      RCLike.inner_apply, map_mul, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = ((sourceTCos : Complex) * sourceTCos) * psi 0 +
          ((sourceTCos : Complex) *
            (star (phaseAmplitude (Real.pi / 4)) * sourceTSin)) * psi 1 := by
        have hstar :
            (starRingEnd Complex) (phaseAmplitude (Real.pi / 4)) =
              star (phaseAmplitude (Real.pi / 4)) := rfl
        rw [hstar]
        ring
      _ = _ := by
        rw [sourceTCos_sq_complex, sourceTState_upper_cross]
        simp only [blochProjector, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.one_apply, blochOperator_apply_zero, tBloch,
          PiLp.smul_apply, PiLp.add_apply]
        push_cast
        rw [sourceTParameter_complex_eq_inv_sqrt_three]
        ring
  · change
      ((InnerProductSpace.rankOne Complex sourceTState sourceTState) psi) 1 =
        (blochProjector tBloch psi) 1
    rw [InnerProductSpace.rankOne_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
      RCLike.inner_apply, map_mul, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = (phaseAmplitude (Real.pi / 4) * sourceTSin * sourceTCos) * psi 0 +
          (phaseAmplitude (Real.pi / 4) * star (phaseAmplitude (Real.pi / 4))) *
            ((sourceTSin : Complex) * sourceTSin) * psi 1 := by
        have hstar :
            (starRingEnd Complex) (phaseAmplitude (Real.pi / 4)) =
              star (phaseAmplitude (Real.pi / 4)) := rfl
        rw [hstar]
        ring
      _ = _ := by
        rw [sourceTState_lower_cross, phaseAmplitude_mul_conj,
          sourceTSin_sq_complex]
        simp only [blochProjector, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.one_apply, blochOperator_apply_one, tBloch,
          PiLp.smul_apply, PiLp.add_apply]
        push_cast
        rw [sourceTParameter_complex_eq_inv_sqrt_three]
        ring
end QEC.Distillation.OneQubitMagic
