-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:18:36.570572+00:00
-- url     : https://prove2.me/submissions/79f62e9c-9fab-4446-9a12-027248049bf5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
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
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedPathEquiv_append
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_succ
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathEnoughMassAux_succ
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathEnoughMassAux_zero
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_succ
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_succ
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_zero
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNestedInputChannel_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorPortRecordTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegisterTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupChannel_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorReindexChannel_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStageInstrument_complete
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSuccessorRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortComplementIdealState_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorCoordinateOperator_succ
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryAt_map
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedPathEquiv_append
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_succ
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_zero
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_succ
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_succ
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_zero
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegisterTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoRouting_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthChildResources_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthSuccessorRouting_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortTransport_apply_basis
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
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem decodedRetryPoolNestedPathEquiv_symm_succ_global
    (m w stage : Nat)
    (path : routedDepthOutputSlots m w (stage + 1)) :
    (decodedRetryPoolNestedPathEquiv m w (stage + 1)).symm path =
      ((decodedRetryPoolNestedPathEquiv m w stage).symm
          (routedDepthOutputPathInit m w stage path),
        decodedRetryPoolLogicalSiteFinEquiv m w
          (routedDepthOutputPathLast m w stage path)) := by
  apply (decodedRetryPoolNestedPathEquiv m w (stage + 1)).injective
  simp only [Equiv.apply_symm_apply,
    decodedRetryPoolNestedPathEquiv_append, Equiv.symm_apply_apply]
  exact (routedDepthOutputPath_append_init_last m w stage path).symm
private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux_append_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (port : LogicalSite m w)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
        h hdegree z q hz previous hstage
          (routedDepthOutputPathAppend m w previous.1 priorPath port) rho =
      decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
        h hdegree z q previous hstage port
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
            h hdegree z q hz previous priorPath rho) := by
  classical
  simpa only [
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux,
    decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator,
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux,
    routedDepthOutputPathInit_append, routedDepthOutputPathLast_append] using
    (bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
      (logicalOutputCount m w) previous.1
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz previous.1 previous.2)
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q previous hstage)
      (decodedRetryPoolSuccessorStageInstrument_complete
        h hdegree z q previous hstage)
      (fun priorOutcome =>
        decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q previous.1 previous.2 priorPath priorOutcome = true)
      (fun successorOutcome =>
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q previous hstage port successorOutcome = true)
      ((decodedRetryPoolNestedPathEquiv m w previous.1).symm priorPath)
      rho.toOperator)
private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_outer
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz (previous.1 + 1) hstage path rho =
      tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w
          (routedDepthOutputPathLast m w previous.1 path))
        (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage path rho) := by
  classical
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
  rw [decodedRetryPoolNestedPathEquiv_symm_succ_global m w stage path]
  rw [nestedTensorCoordinateOperator_succ]
  apply congrArg
    (tensorPowerCoordinateOperator (logicalOutputCount m w)
      (decodedRetryPoolLogicalSiteFinEquiv m w
        (routedDepthOutputPathLast m w stage path)))
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
    bindNestedFilteredCoordinateOperator
  rw [decodedRetryPoolProtocolInstrumentAux_succ]
  simp only [decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ,
    Bool.and_eq_true]
  unfold decodedRetryPoolProtocolSuccessorInstrumentAux
    decodedRetryPoolNestedSuccessorStageInstrument
  rfl
private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
        h hdegree z q hz previous priorPath rho =
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz previous.1 previous.2 priorPath rho := by
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
    nestedFilteredPredecessorCoordinateOperator
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
  rfl
private theorem
    decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (previous : Fin z) (hstage : previous.1 + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q previous) ×
        LogicalSite m w))) :
    tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
          h hdegree z q previous hstage port A) =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q previous.1 hstage port A := by
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
    filteredBranchOperatorSum
  rfl
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
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz (previous.1 + 1) hstage path rho =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q previous.1 hstage
          (routedDepthOutputPathLast m w previous.1 path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
            h hdegree z q hz previous.1 previous.2
              (routedDepthOutputPathInit m w previous.1 path) rho) := by
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_outer]
  have houter :
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage path rho =
        decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
          h hdegree z q previous hstage
            (routedDepthOutputPathLast m w previous.1 path)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
              h hdegree z q hz previous
                (routedDepthOutputPathInit m w previous.1 path) rho) := by
    calc
      _ = decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage
            (routedDepthOutputPathAppend m w previous.1
              (routedDepthOutputPathInit m w previous.1 path)
              (routedDepthOutputPathLast m w previous.1 path)) rho := by
          apply congrArg (fun selectedPath =>
            decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
              h hdegree z q hz previous hstage selectedPath rho)
          exact
            (routedDepthOutputPath_append_init_last
              m w previous.1 path).symm
      _ = _ :=
        decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux_append_eq
          h hdegree z q hz previous hstage
            (routedDepthOutputPathInit m w previous.1 path)
            (routedDepthOutputPathLast m w previous.1 path) rho
  rw [houter]
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux_eq]
  exact decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator_eq
    h hdegree z q previous hstage
      (routedDepthOutputPathLast m w previous.1 path)
      (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz previous.1 previous.2
          (routedDepthOutputPathInit m w previous.1 path) rho)
end QEC.Distillation.HH18Parameterized
