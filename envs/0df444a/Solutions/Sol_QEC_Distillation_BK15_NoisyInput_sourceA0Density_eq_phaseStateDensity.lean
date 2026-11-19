-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.sourceA0Density_eq_phaseStateDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:06:38.330072+00:00
-- url     : https://prove2.me/submissions/a6af00dd-84f9-4743-86c2-7371ec58768f

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hMagicState_eq_sourceHDensity
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_neg_pi_div_eight
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_pi_div_eight
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
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
namespace BK15
namespace NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem sourceA0Transport_sourceHState :
    sourceA0Transport sourceHState =
      phaseAmplitude (-Real.pi / 8) • phaseState (Real.pi / 4) := by
  have hproduct :
      phaseAmplitude (-Real.pi / 8) * phaseAmplitude (Real.pi / 4) =
        (Real.cos (Real.pi / 8) : Complex) +
          (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
    rw [← phaseAmplitude_add]
    rw [show -Real.pi / 8 + Real.pi / 4 = Real.pi / 8 by ring]
    exact phaseAmplitude_pi_div_eight
  ext bit
  fin_cases bit
  · change hadamardOperator (phaseInverseOperator sourceHState) 0 =
      phaseAmplitude (-Real.pi / 8) * phaseState (Real.pi / 4) 0
    rw [hadamardOperator_apply_zero, phaseInverseOperator_apply_zero,
      phaseInverseOperator_apply_one, sourceHState_apply_zero,
      sourceHState_apply_one, phaseState_apply_zero,
      phaseAmplitude_neg_pi_div_eight]
    ring
  · change hadamardOperator (phaseInverseOperator sourceHState) 1 =
      phaseAmplitude (-Real.pi / 8) * phaseState (Real.pi / 4) 1
    rw [hadamardOperator_apply_one, phaseInverseOperator_apply_zero,
      phaseInverseOperator_apply_one, sourceHState_apply_zero,
      sourceHState_apply_one, phaseState_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.cos (Real.pi / 8) : Complex) -
            (-Complex.I) * (Real.sin (Real.pi / 8) : Complex)) =
          (Real.sqrt 2 : Complex)⁻¹ *
            (phaseAmplitude (-Real.pi / 8) * phaseAmplitude (Real.pi / 4)) := by
              rw [hproduct]
              ring
      _ = phaseAmplitude (-Real.pi / 8) *
          ((Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude (Real.pi / 4)) := by
            ring
private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x bit
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)) x).ofLp bit =
    ((InnerProductSpace.rankOne Complex psi psi) x).ofLp bit
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply]
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi bit) =
        (z * star z) * inner Complex psi x * psi bit := by ring
    _ = inner Complex psi x * psi bit := by rw [hz]; ring
namespace BK15Epsilon
end BK15Epsilon
section
set_option maxRecDepth 65536
end
end NoisyInput
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.NoisyInput
theorem _root_.solution :
    sourceA0Density = phaseStateDensity (Real.pi / 4) := by
  rw [sourceA0Density, hMagicState_eq_sourceHDensity]
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator, sourceHDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne, sourceA0Transport_sourceHState,
    phaseStateDensity_toOperator]
  exact rankOne_global_phase (phaseAmplitude (-Real.pi / 8))
    (phaseState (Real.pi / 4)) (phaseAmplitude_mul_conj (-Real.pi / 8))
end QEC.Distillation.BK15.NoisyInput
