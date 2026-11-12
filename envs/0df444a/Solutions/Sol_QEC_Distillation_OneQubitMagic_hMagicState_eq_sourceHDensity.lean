-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hMagicState_eq_sourceHDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:00:01.7718+00:00
-- url     : https://prove2.me/submissions/7a2abd1f-25d9-4210-a678-017c1ad2cd80

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
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


attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
section
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
private theorem cos_pi_div_eight_sq :
    Real.cos (Real.pi / 8) ^ 2 = 1 / 2 + Real.sqrt 2 / 4 := by
  rw [Real.cos_sq]
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  ring
private theorem sin_pi_div_eight_sq :
    Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.sqrt 2 / 4 := by
  rw [Real.sin_sq, cos_pi_div_eight_sq]
  ring
private theorem sin_pi_div_eight_mul_cos_pi_div_eight :
    Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = Real.sqrt 2 / 4 := by
  calc
    Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) =
        Real.sin (2 * (Real.pi / 8)) / 2 := by
          rw [Real.sin_two_mul]
          ring
    _ = Real.sqrt 2 / 4 := by
      rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
      ring
private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem rankOne_apply_coordinate
    (u v x : QubitSpace) (b : Fin 2) :
    ((InnerProductSpace.rankOne Complex u v).toLinearMap x) b =
      (inner Complex v x) * u b := by
  change ((InnerProductSpace.rankOne Complex u v) x).ofLp b = _
  rw [InnerProductSpace.rankOne_apply]
  rfl
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
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : hMagicState = sourceHDensity := by
  apply densityOperator_ext_toOperator
  rw [sourceHDensity_toOperator]
  change blochProjector hBloch =
    (InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  have hsqrt_inv :
      ((1 / Real.sqrt 2 : Real) : Complex) = (Real.sqrt 2 : Complex) / 2 := by
    push_cast
    field_simp [hsqrt_ne]
    rw [pow_two, hsqrt_sq]
  have hcos_sq :
      (Real.cos (Real.pi / 8) : Complex) ^ 2 =
        (1 / 2 + Real.sqrt 2 / 4 : Real) := by
    rw [pow_two]
    exact_mod_cast (show
      Real.cos (Real.pi / 8) * Real.cos (Real.pi / 8) =
        1 / 2 + Real.sqrt 2 / 4 by
          simpa [pow_two] using cos_pi_div_eight_sq)
  have hsin_sq :
      (Real.sin (Real.pi / 8) : Complex) ^ 2 =
        (1 / 2 - Real.sqrt 2 / 4 : Real) := by
    rw [pow_two]
    exact_mod_cast (show
      Real.sin (Real.pi / 8) * Real.sin (Real.pi / 8) =
        1 / 2 - Real.sqrt 2 / 4 by
          simpa [pow_two] using sin_pi_div_eight_sq)
  have hsin_cos :
      (Real.sin (Real.pi / 8) : Complex) *
          (Real.cos (Real.pi / 8) : Complex) =
        (Real.sqrt 2 / 4 : Real) := by
    exact_mod_cast sin_pi_div_eight_mul_cos_pi_div_eight
  have hcos_sin :
      (Real.cos (Real.pi / 8) : Complex) *
          (Real.sin (Real.pi / 8) : Complex) =
        (Real.sqrt 2 / 4 : Real) := by
    rw [mul_comm]
    exact hsin_cos
  have hangle : Real.pi * (1 / 8 : Real) = Real.pi / 8 := by
    ring
  ext psi b
  fin_cases b
  · change blochProjector hBloch psi 0 =
      ((InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap psi) 0
    rw [rankOne_apply_coordinate]
    change (2 : Complex)⁻¹ * (psi 0 + (blochOperator hBloch psi) 0) = _
    simp only [blochOperator_apply_zero, hBloch, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply]
    change _ =
      (psi 0 * star (sourceHState 0) + psi 1 * star (sourceHState 1)) * sourceHState 0
    rw [sourceHState_apply_zero, sourceHState_apply_one]
    rw [Complex.star_def]
    simp only [Complex.conj_ofReal]
    ring_nf
    have hcross :
        psi 1 * (Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex) =
          psi 1 * (Real.sqrt 2 / 4 : Real) := by
      calc
        _ = psi 1 * ((Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex)) := by ring
        _ = _ := by rw [hcos_sin]
    rw [hangle, hcos_sq, hcross]
    field_simp [hsqrt_ne]
    rw [hsqrt_inv]
    push_cast
    ring
  · change blochProjector hBloch psi 1 =
      ((InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap psi) 1
    rw [rankOne_apply_coordinate]
    change (2 : Complex)⁻¹ * (psi 1 + (blochOperator hBloch psi) 1) = _
    simp only [blochOperator_apply_one, hBloch, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply]
    change _ =
      (psi 0 * star (sourceHState 0) + psi 1 * star (sourceHState 1)) * sourceHState 1
    rw [sourceHState_apply_zero, sourceHState_apply_one]
    rw [Complex.star_def]
    simp only [Complex.conj_ofReal]
    ring_nf
    have hcross :
        psi 0 * (Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex) =
          psi 0 * (Real.sqrt 2 / 4 : Real) := by
      calc
        _ = psi 0 * ((Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex)) := by ring
        _ = _ := by rw [hcos_sin]
    rw [hangle, hsin_sq, hcross]
    field_simp [hsqrt_ne]
    rw [hsqrt_inv]
    push_cast
    ring
end QEC.Distillation.OneQubitMagic
