-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.selectedLogicalPortIdealMarginal_eq_aZeroDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:08:40.618911+00:00
-- url     : https://prove2.me/submissions/103f08b6-534e-4f03-ac98-4ccc9a90b949

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortComplementIdealState_apply
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
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalTInv_eq_allSitePhase_neg_pi_div_four
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aZeroDensity_rankOne
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_inner_self
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_allSitePhase_apply
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
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
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
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator
attribute [local simp] QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_adverse
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_favorable
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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


attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
private theorem selectedLogicalPortAnchorBitstring_apply_port (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    selectedLogicalPortAnchorBitstring m w port bits port = 0 := by
  simp [selectedLogicalPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    selectedLogicalPortSubsystem]
private theorem selectedLogicalPortRecombineBitstring_apply_port (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) port =
      left (selectedLogicalPortCoordinate m w port) := by
  simp only [FiniteSubsystem.recombineBitstring]
  rw [dif_pos (by simp [selectedLogicalPortSubsystem])]
  let coordinate : (selectedLogicalPortSubsystem m w port).SelectedCoordinates :=
    ⟨port, by simp [selectedLogicalPortSubsystem]⟩
  change left coordinate = left (selectedLogicalPortCoordinate m w port)
  rw [selectedLogicalPortCoordinate_eq m w port coordinate]
private theorem selectedLogicalPortRecombineBitstring_apply_ne (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
    (site : LogicalSite m w) (hsite : site ≠ port) :
    (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) site =
      selectedLogicalPortAnchorBitstring m w port right site := by
  simp [selectedLogicalPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    selectedLogicalPortSubsystem, hsite]
private theorem selectedLogicalPortHammingWeight_recombine (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
      ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right))) =
      (selectedLogicalPortBitstringEquiv m w port left).val +
        Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port right)) := by
  classical
  generalize hbit : selectedLogicalPortBitstringEquiv m w port left = bit
  fin_cases bit
  · have hleft : left (selectedLogicalPortCoordinate m w port) = 0 := by
      simpa [selectedLogicalPortBitstringEquiv] using hbit
    have heq :
        (selectedLogicalPortSubsystem m w port).recombineBitstring (left, right) =
          selectedLogicalPortAnchorBitstring m w port right := by
      funext site
      by_cases hsite : site = port
      · subst site
        rw [selectedLogicalPortRecombineBitstring_apply_port,
          selectedLogicalPortAnchorBitstring_apply_port, hleft]
      · exact selectedLogicalPortRecombineBitstring_apply_ne m w port left right site hsite
    simp [heq]
  · have hleft : left (selectedLogicalPortCoordinate m w port) = 1 := by
      simpa [selectedLogicalPortBitstringEquiv] using hbit
    have hsupp :
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right))) =
          insert port
            (Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
              (selectedLogicalPortAnchorBitstring m w port right))) := by
      ext site
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and,
        Coding.PauliSymplectic.bitstringWordEquiv_apply]
      by_cases hsite : site = port
      · subst site
        norm_num [
          selectedLogicalPortRecombineBitstring_apply_port,
          selectedLogicalPortAnchorBitstring_apply_port, hleft]
        exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
      · have happly :=
          selectedLogicalPortRecombineBitstring_apply_ne m w port left right site hsite
        simp only [happly, hsite, false_or]
    have hnotmem : port ∉
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port right)) := by
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter]
      simp [Coding.PauliSymplectic.bitstringWordEquiv_apply,
        selectedLogicalPortAnchorBitstring_apply_port]
      rfl
    simp only [Coding.HammingWeight, hsupp,
      Finset.card_insert_of_notMem hnotmem]
    omega
private theorem selectedLogicalPortMagicState_recombine_amplitude (m w : Nat)
    (port : LogicalSite m w)
    (left : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates)
    (right : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
        ((selectedLogicalPortSubsystem m w port).recombineBitstring (left, right)) =
      aZeroState (selectedLogicalPortBitstringEquiv m w port left) *
        selectedLogicalPortComplementIdealState m w port right := by
  rw [Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    selectedLogicalPortComplementIdealState_apply,
    Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    selectedLogicalPortHammingWeight_recombine]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  generalize hbit : selectedLogicalPortBitstringEquiv m w port left = bit
  fin_cases bit
  all_goals simp [aZeroState, OneQubitMagic.phaseState,
    Triorthogonal.BinaryRowFamily.piDivFourPhase]
  all_goals field_simp [hsqrt_ne]
  all_goals ring
private theorem selectedLogicalPortTransport_symm_apply (m w : Nat)
    (port : LogicalSite m w) (psi : QubitSpace)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).SelectedCoordinates) :
    (selectedLogicalPortTransport m w port).symm psi bits =
      psi (selectedLogicalPortBitstringEquiv m w port bits) := by
  have hinner := (selectedLogicalPortTransport m w port).map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((selectedLogicalPortTransport m w port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [selectedLogicalPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
private theorem selectedLogicalPortRegisterFactorization_symm_tmul_apply (m w : Nat)
    (port : LogicalSite m w)
    (leftState : (selectedLogicalPortSubsystem m w port).selectedSystem)
    (rightState : (selectedLogicalPortSubsystem m w port).complementSystem)
    (bits : Qubit.Bitstring (LogicalSite m w)) :
    (selectedLogicalPortSubsystem m w port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) bits =
      leftState ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1 *
        rightState ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2 := by
  have hinner := (selectedLogicalPortSubsystem m w port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((selectedLogicalPortSubsystem m w port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [FiniteSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
private theorem selectedLogicalPortMagicState_factorization (m w : Nat)
    (port : LogicalSite m w) :
    (selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) =
      (selectedLogicalPortTransport m w port).symm aZeroState ⊗ₜ[Complex]
        selectedLogicalPortComplementIdealState m w port := by
  apply (selectedLogicalPortSubsystem m w port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext bits
  change Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) bits =
    (selectedLogicalPortSubsystem m w port).registerFactorization.symm
      ((selectedLogicalPortTransport m w port).symm aZeroState ⊗ₜ[Complex]
        selectedLogicalPortComplementIdealState m w port) bits
  rw [selectedLogicalPortRegisterFactorization_symm_tmul_apply,
    selectedLogicalPortTransport_symm_apply]
  have hsplit :
      (selectedLogicalPortSubsystem m w port).recombineBitstring
          ((selectedLogicalPortSubsystem m w port).splitBitstring bits) = bits := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      (selectedLogicalPortSubsystem m w port).bitstringFactorization.symm_apply_apply bits
  calc
    Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) bits =
        Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
          ((selectedLogicalPortSubsystem m w port).recombineBitstring
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits)) := by rw [hsplit]
    _ = aZeroState
          (selectedLogicalPortBitstringEquiv m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1) *
          selectedLogicalPortComplementIdealState m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2 := by
          exact selectedLogicalPortMagicState_recombine_amplitude m w port
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).1
            ((selectedLogicalPortSubsystem m w port).splitBitstring bits).2
private theorem phaseAmplitude_nat_mul (theta : ℝ) (n : Nat) :
    OneQubitMagic.phaseAmplitude (n * theta) =
      OneQubitMagic.phaseAmplitude theta ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, OneQubitMagic.phaseAmplitude_add,
        ih, one_mul, pow_succ]
private theorem logicalTInv_logicalMagicState (m w : Nat) :
    HH18PuncturedReedMuller.logicalTInv w m
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) =
        logicalPlus m w := by
  ext bits
  rw [HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four,
    Triorthogonal.allSitePhase_apply]
  simp only [Triorthogonal.BinaryRowFamily.logicalMagicState_apply,
    logicalPlus, Triorthogonal.BinaryRowFamily.logicalPlusState_apply,
    Triorthogonal.BinaryRowFamily.piDivFourPhase]
  rw [show -Real.pi / 4 *
      (Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
        (LogicalSite m w) bits) : Real) =
      -(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
        (LogicalSite m w) bits) : Nat) * (Real.pi / 4) by ring]
  have hphase :
      OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
        OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
          Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) = 1 := by
    rw [← phaseAmplitude_nat_mul]
    rw [← OneQubitMagic.phaseAmplitude_add]
    convert OneQubitMagic.phaseAmplitude_zero using 1
    ring_nf
  calc
    OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
        (Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (LogicalSite m w) bits)) =
        (OneQubitMagic.phaseAmplitude
          (-(Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
            (LogicalSite m w) bits) : Nat) * (Real.pi / 4)) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (LogicalSite m w) bits)) *
          Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) := by ring
    _ = Triorthogonal.BinaryRowFamily.logicalUniformScalar (LogicalSite m w) := by
      rw [hphase]
      ring
private theorem idealLogicalTOutputState_eq_logicalMagicState (m w : Nat) :
    idealLogicalTOutputState m w =
      Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w) := by
  apply (HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv.injective
  change (HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv
      ((HH18PuncturedReedMuller.logicalTInv w m).toLinearEquiv.symm
        (logicalPlus m w)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (logicalTInv_logicalMagicState m w).symm
private theorem selectedLogicalPortComplementIdealState_inner_self (m w : Nat)
    (port : LogicalSite m w) :
    inner Complex (selectedLogicalPortComplementIdealState m w port)
      (selectedLogicalPortComplementIdealState m w port) = 1 := by
  have hglobal : inner Complex
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w))
      (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)) = 1 :=
    Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self (LogicalSite m w)
  have hlocal : inner Complex
      ((selectedLogicalPortTransport m w port).symm aZeroState)
      ((selectedLogicalPortTransport m w port).symm aZeroState) = 1 := by
    calc
      inner Complex ((selectedLogicalPortTransport m w port).symm aZeroState)
          ((selectedLogicalPortTransport m w port).symm aZeroState) =
          inner Complex
            ((selectedLogicalPortTransport m w port)
              ((selectedLogicalPortTransport m w port).symm aZeroState))
            ((selectedLogicalPortTransport m w port)
              ((selectedLogicalPortTransport m w port).symm aZeroState)) :=
            ((selectedLogicalPortTransport m w port).map_inner _ _).symm
      _ = inner Complex aZeroState aZeroState := by
            simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
      _ = 1 := by
            rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
            norm_num
  have hfactorNorm : inner Complex
      ((selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)))
      ((selectedLogicalPortSubsystem m w port).registerFactorization
        (Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w))) = 1 := by
    rw [(selectedLogicalPortSubsystem m w port).registerFactorization.map_inner]
    exact hglobal
  rw [selectedLogicalPortMagicState_factorization, TensorProduct.inner_tmul,
    hlocal, one_mul] at hfactorNorm
  exact hfactorNorm
end HH18Parameterized
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat)
    (port : LogicalSite m w) :
    selectedLogicalPortIdealMarginal m w port = aZeroDensity := by
  apply DensityOperator.ext_toOperator
  simp only [selectedLogicalPortIdealMarginal, UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    idealLogicalTOutput, DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [idealLogicalTOutputState_eq_logicalMagicState]
  rw [selectedLogicalPortMagicState_factorization]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [selectedLogicalPortComplementIdealState_inner_self]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact aZeroDensity_rankOne.symm
end QEC.Distillation.HH18Parameterized
