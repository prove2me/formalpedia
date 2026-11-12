-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hResourceTransport_sourceHState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:04:12.2962+00:00
-- url     : https://prove2.me/submissions/83267b3c-dd8e-4b35-b1f2-d97a695f6fc6

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_pi_div_eight
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_neg_pi_div_eight
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    hResourceTransport sourceHState =
      phaseAmplitude (Real.pi / 8) • phaseState (-Real.pi / 4) := by
  have hproduct :
      phaseAmplitude (Real.pi / 8) * phaseAmplitude (-Real.pi / 4) =
        (Real.cos (Real.pi / 8) : Complex) -
          (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
    rw [← phaseAmplitude_add]
    rw [show Real.pi / 8 + -Real.pi / 4 = -Real.pi / 8 by ring]
    exact phaseAmplitude_neg_pi_div_eight
  ext b
  fin_cases b
  · change hadamardOperator (phaseOperator sourceHState) 0 =
      phaseAmplitude (Real.pi / 8) * phaseState (-Real.pi / 4) 0
    rw [hadamardOperator_apply_zero, phaseOperator_apply_zero,
      phaseOperator_apply_one, sourceHState_apply_zero, sourceHState_apply_one,
      phaseState_apply_zero, phaseAmplitude_pi_div_eight]
    ring
  · change hadamardOperator (phaseOperator sourceHState) 1 =
      phaseAmplitude (Real.pi / 8) * phaseState (-Real.pi / 4) 1
    rw [hadamardOperator_apply_one, phaseOperator_apply_zero,
      phaseOperator_apply_one, sourceHState_apply_zero, sourceHState_apply_one,
      phaseState_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.cos (Real.pi / 8) : Complex) -
            Complex.I * (Real.sin (Real.pi / 8) : Complex)) =
          (Real.sqrt 2 : Complex)⁻¹ *
            (phaseAmplitude (Real.pi / 8) * phaseAmplitude (-Real.pi / 4)) := by
              rw [hproduct]
              ring
      _ = phaseAmplitude (Real.pi / 8) *
          ((Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude (-Real.pi / 4)) := by
            ring
end QEC.Distillation.OneQubitMagic
