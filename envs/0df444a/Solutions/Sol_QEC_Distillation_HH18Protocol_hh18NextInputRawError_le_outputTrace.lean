-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18NextInputRawError_le_outputTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:05:12.889429+00:00
-- url     : https://prove2.me/submissions/ddca2ff1-4071-4e99-8bd6-711cfebad811

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18LogicalOutputTransport_idealOutput
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
import Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_branch_aZero
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
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
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
import Theorems.Thm_QEC_Semantics_operatorNorm_projection_le
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_adverse
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_favorable
attribute [local simp] QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Protocol.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Protocol.prepareMeasuredResources_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
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
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Semantics.traceNorm_neg


section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
@[simp] private theorem hh18LogicalOutputTransport_apply
    (psi : LogicalRegister) (bit : Fin 2) :
    hh18LogicalOutputTransport psi bit = psi (fun _ => bit) := by
  rfl
private theorem aBasisInstrument_bornWeight_eq_projectorProbability
    (outcome : StabilizerOutcome) (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight outcome rho =
      aBasisProjectorProbability outcome rho := by
  classical
  unfold FiniteInstrument.bornWeight aBasisProjectorProbability
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single outcome]
  · simp only [aBasisInstrument, aBasisDephasingKrausFamily, id_eq,
      ↓reduceIte]
    change Complex.re (LinearMap.trace Complex QubitSpace
      (aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome)))) = _
    rw [aBasisProjector_adjoint]
    calc
      Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (rho.toOperator * aBasisProjector outcome))) =
          Complex.re (LinearMap.trace Complex QubitSpace
            ((aBasisProjector outcome * rho.toOperator) *
              aBasisProjector outcome)) := by
            congr 2
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome *
            (aBasisProjector outcome * rho.toOperator))) := by
            rw [LinearMap.trace_mul_comm]
      _ = Complex.re (LinearMap.trace Complex QubitSpace
          (aBasisProjector outcome * rho.toOperator)) := by
            rw [← mul_assoc, aBasisProjector_idempotent]
  · intro other hother
    simp [aBasisInstrument, aBasisDephasingKrausFamily, hother]
private theorem aBasisProjectorProbability_transport
    (rho : DensityOperator LogicalRegister) :
    aBasisProjectorProbability .negative
        (hh18LogicalOutputTransport.conjDensity rho) =
      (LinearMap.trace Complex LogicalRegister
        (hh18LogicalOutputTransport.symm.conjOperator
          (aBasisProjector .negative) * rho.toOperator)).re := by
  unfold aBasisProjectorProbability
  rw [UnitaryTransport.conjDensity_toOperator]
  have hproduct :
      aBasisProjector .negative *
          hh18LogicalOutputTransport.conjOperator rho.toOperator =
        hh18LogicalOutputTransport.conjOperator
          (hh18LogicalOutputTransport.symm.conjOperator
            (aBasisProjector .negative) * rho.toOperator) := by
    rw [UnitaryTransport.conjOperator_mul,
      hh18LogicalOutputTransport.conjOperator_symm_conjOperator]
  rw [hproduct, hh18LogicalOutputTransport.trace_conjOperator]
private theorem negative_aBasisProjector_pullback_isStarProjection :
    IsStarProjection
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative)) := by
  rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
  constructor
  · change
      hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative) *
          hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative) =
        hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
    rw [← UnitaryTransport.conjOperator_mul, aBasisProjector_idempotent]
  · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
    change
      LinearMap.adjoint
          (hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)) =
        hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
    rw [UnitaryTransport.conjOperator_adjoint, aBasisProjector_adjoint]
private theorem transported_ideal_negative_aBasis_weight_zero :
    aBasisInstrument.bornWeight .negative
      (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) = 0 := by
  rw [hh18LogicalOutputTransport_idealOutput]
  rw [FiniteInstrument.bornWeight, aBasisInstrument_branch_aZero]
  have hne : (StabilizerOutcome.negative : StabilizerOutcome) ≠ .positive := by decide
  rw [if_neg hne]
  norm_num
private theorem pulled_negative_projector_ideal_trace_zero :
    (LinearMap.trace Complex LogicalRegister
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative) * idealLogicalTOutput.toOperator)).re = 0 := by
  calc
    (LinearMap.trace Complex LogicalRegister
      (hh18LogicalOutputTransport.symm.conjOperator
        (aBasisProjector .negative) * idealLogicalTOutput.toOperator)).re =
        aBasisProjectorProbability .negative
          (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) := by
          symm
          exact aBasisProjectorProbability_transport idealLogicalTOutput
    _ = aBasisInstrument.bornWeight .negative
          (hh18LogicalOutputTransport.conjDensity idealLogicalTOutput) := by
          symm
          exact aBasisInstrument_bornWeight_eq_projectorProbability .negative _
    _ = 0 := transported_ideal_negative_aBasis_weight_zero
end HH18Protocol
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputRawError epsilon ≤
      hh18OutputTraceError
        (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
        idealLogicalTOutput := by
  let P : Operator LogicalRegister :=
    hh18LogicalOutputTransport.symm.conjOperator (aBasisProjector .negative)
  let rho : DensityOperator LogicalRegister :=
    (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
  have hprojector : IsStarProjection P :=
    negative_aBasisProjector_pullback_isStarProjection
  have hideal :
      (LinearMap.trace Complex LogicalRegister (P * idealLogicalTOutput.toOperator)).re =
        0 :=
    pulled_negative_projector_ideal_trace_zero
  have hraw :
      hh18NextInputRawError epsilon =
        (LinearMap.trace Complex LogicalRegister (P * rho.toOperator)).re := by
    unfold hh18NextInputRawError hh18TransportedAcceptedOutput
    rw [aBasisInstrument_bornWeight_eq_projectorProbability]
    exact aBasisProjectorProbability_transport rho
  have hcenter :
      (LinearMap.trace Complex LogicalRegister (P * rho.toOperator)).re =
        (LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re := by
    rw [mul_sub, map_sub, Complex.sub_re, hideal, sub_zero]
  calc
    hh18NextInputRawError epsilon =
        (LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re := hraw.trans hcenter
    _ ≤ |(LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))).re| := le_abs_self _
    _ ≤ ‖LinearMap.trace Complex LogicalRegister
          (P * (rho.toOperator - idealLogicalTOutput.toOperator))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm (P * (rho.toOperator - idealLogicalTOutput.toOperator)) :=
      norm_trace_le_traceNorm _
    _ ≤ operatorNorm P *
          traceNorm (rho.toOperator - idealLogicalTOutput.toOperator) :=
      traceNorm_mul_left_le _ _
    _ ≤ 1 * traceNorm (rho.toOperator - idealLogicalTOutput.toOperator) := by
      exact mul_le_mul_of_nonneg_right
        (operatorNorm_projection_le P hprojector) (traceNorm_nonneg _)
    _ = hh18OutputTraceError rho idealLogicalTOutput := by
      simp [hh18OutputTraceError]
end QEC.Distillation.HH18Protocol
