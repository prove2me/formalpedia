-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.sourceTAcceptedBranch_to_phaseStateDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:24:31.993209+00:00
-- url     : https://prove2.me/submissions/1511094f-4b45-4328-89cf-306e930096f8

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
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
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_compose
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_identity
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_oneQubit
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_xor
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngle_cos
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
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
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTEvenBranch_xor_discard
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTEvenOutput_global_phase
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTGlobalPhase_norm
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
import Theorems.Thm_QEC_Distillation_phaseNormalize_matrix
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
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_compose
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_identity
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_oneQubit
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.hAngle_cos
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
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
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
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
attribute [local simp] QEC.Distillation.phaseNormalize_matrix
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
namespace IdealResourceUniversality
open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators
private theorem densityOperator_ext_toOperator {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H} (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x b
  change (inner Complex (z • psi) x) * (z • psi) b =
    (inner Complex psi x) * psi b
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi b) =
        (z * star z) * inner Complex psi x * psi b := by ring
    _ = inner Complex psi x * psi b := by rw [hz]; ring
namespace SourceTPreparationAcceptedTrace
end SourceTPreparationAcceptedTrace
private theorem sourceTGlobalPhase_mul_conj :
    sourceTGlobalPhase * star sourceTGlobalPhase = 1 := by
  rw [mul_comm]
  change (starRingEnd Complex) sourceTGlobalPhase * sourceTGlobalPhase = 1
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
    sourceTGlobalPhase_norm]
  norm_num
end IdealResourceUniversality
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.IdealResourceUniversality
open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators
namespace QEC.Distillation.IdealResourceUniversality
theorem _root_.solution :
    (QuantumChannel.unitaryConj hadamardTransport).mapDensity
        ((QuantumChannel.comp TwoQubit.secondQubitDiscard
          (QuantumChannel.unitaryConj TwoQubit.xorTransport)).mapDensity
            sourceTEvenBranch) =
      phaseStateDensity (-Real.pi / 6) := by
  rw [sourceTEvenBranch_xor_discard]
  apply densityOperator_ext_toOperator
  have hweight : 0 < sourceTEvenWeight := by
    rw [sourceTEvenWeight_eq_two_thirds]
    norm_num
  have hfirst :
      TwoQubit.zzEvenBranchFirstQubit sourceTTwoQubitState hweight =
        sourceTEvenFirstQubit := by
    rfl
  have hnorm : ‖sourceTEvenFirstQubit‖ = 1 := by
    rw [← hfirst]
    exact TwoQubit.zzEvenBranchFirstQubit_norm sourceTTwoQubitState hweight
  have hinput :
      (TwoQubit.zzEvenBranchFirstDensity sourceTTwoQubitState
        hweight).toOperator =
        (InnerProductSpace.rankOne Complex sourceTEvenFirstQubit
          sourceTEvenFirstQubit).toLinearMap := by
    dsimp only [TwoQubit.zzEvenBranchFirstDensity]
    rw [DensityOperator.pureOfNonzero_toOperator,
      hfirst, inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  rw [QuantumChannel.mapDensity_toOperator, QuantumChannel.unitaryConj_apply,
    hinput, QuditSubsystem.conjOperator_rankOne,
    phaseStateDensity_toOperator]
  change (InnerProductSpace.rankOne Complex
      (hadamardOperator sourceTEvenFirstQubit)
      (hadamardOperator sourceTEvenFirstQubit)).toLinearMap = _
  rw [sourceTEvenOutput_global_phase]
  exact rankOne_global_phase sourceTGlobalPhase
    (phaseState (-Real.pi / 6)) sourceTGlobalPhase_mul_conj
end QEC.Distillation.IdealResourceUniversality
