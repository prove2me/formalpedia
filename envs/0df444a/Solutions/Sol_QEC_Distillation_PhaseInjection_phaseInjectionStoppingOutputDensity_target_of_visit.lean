-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseInjectionStoppingOutputDensity_target_of_visit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:51:59.626404+00:00
-- url     : https://prove2.me/submissions/2d62fff4-fa46-4feb-b886-5a535ad308b7

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingTrace_output_target_of_visit
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_measure
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependCoin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependDeterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependSyndrome
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_ledger_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_clifford
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_discard
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_zeroPreparation
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_operator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_conditionalDensity_toOperator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_ZeroPreparationAdapter_run_toOperator
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependCoin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependDeterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependSyndrome
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.ledger_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_discard
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_zeroPreparation
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_operator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
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
namespace PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
private theorem densityOperator_ext_toOperator {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H} (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem sourceInputDensity_toOperator (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (sourceInputDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [sourceInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, hpsi]
  norm_num
private theorem phaseInjectionHistoryGlobalPhase_norm (theta : Real) (coins : List Bool) :
    ‖phaseInjectionHistoryGlobalPhase theta coins‖ = 1 := by
  induction coins with
  | nil => simp [phaseInjectionHistoryGlobalPhase]
  | cons coin coins ih =>
      rw [phaseInjectionHistoryGlobalPhase, norm_mul,
        oneShotAttemptGlobalPhase_norm, ih]
      norm_num
private theorem phaseInjection_rankOne_global_phase
    (z : Complex) (psi : QubitSpace)
    (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x b
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap x) b =
    ((InnerProductSpace.rankOne Complex psi psi).toLinearMap x) b
  change (inner Complex (z • psi) x) * (z • psi) b =
    (inner Complex psi x) * psi b
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi b) =
        (z * star z) * inner Complex psi x * psi b := by ring
    _ = inner Complex psi x * psi b := by rw [hz]; ring
private theorem phaseInjectionHistoryGlobalPhase_mul_conj
    (theta : Real) (coins : List Bool) :
    phaseInjectionHistoryGlobalPhase theta coins *
      star (phaseInjectionHistoryGlobalPhase theta coins) = 1 := by
  rw [mul_comm]
  change (starRingEnd Complex) (phaseInjectionHistoryGlobalPhase theta coins) *
    phaseInjectionHistoryGlobalPhase theta coins = 1
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
    phaseInjectionHistoryGlobalPhase_norm]
  norm_num
end PhaseInjection
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution {q blocks : Nat} [NeZero q]
    (target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget (0 : ZMod q) target blocks trace) :
    phaseInjectionStoppingOutputDensity (0 : ZMod q) target trace psi hpsi =
      sourceInputDensity (phaseCycleTargetAction q target psi)
        (phaseCycleTargetAction_norm q target psi hpsi) := by
  apply densityOperator_ext_toOperator
  rw [phaseInjectionStoppingOutputDensity,
    DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K,
    phaseInjectionStoppingTrace_output_norm]
  norm_num
  rw [sourceInputDensity_toOperator]
  rw [phaseInjectionStoppingTrace_output_target_of_visit target trace psi hpsi hvisit]
  exact phaseInjection_rankOne_global_phase _ _
    (phaseInjectionHistoryGlobalPhase_mul_conj _ _)
end QEC.Distillation.PhaseInjection
