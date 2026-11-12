-- Prove2me | solution 1 for QEC.Distillation.HH18.hh18_sublogarithmic_distillation_overhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:39:08.41212+00:00
-- url     : https://prove2.me/submissions/73abee3a-4516-4a58-aa57-1dfc12b4563f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
import Definitions.Def_QEC_Results_Distillation_SublogarithmicOverhead
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
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedPathEquiv_append
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchActualOutputError_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchProtocolFamily_polylogarithmicOverhead
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_resourceCount
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_successProbability
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
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
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_logicalOutputCount_eq_binomialUpTo
import Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalInputCount_eq_binomialTail
import Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalTInv_implements_logicalT
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSuccessorRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortComplementIdealState_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssParameters
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalTInv_implements_logicalT
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalT_implements_logicalTInv
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_exists_finite_subunit_gamma_selector
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaSet_bddBelow
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18Gamma_p0_lt_339_div_500
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_mem_parameterInterval
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_parameter_sequence_admissible
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
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
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_resourceCount
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_successProbability
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
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
namespace QEC.Distillation.HH18
open Coding
open Coding.PuncturedReedMuller
open Filter Topology
open Semantics
open Semantics.FiniteInstrument
open QEC.Distillation.HH18PuncturedReedMuller
open HH18SublogarithmicEntropy
open HH18Parameterized
private theorem selected_physical_counts
    (A D j : Nat) :
    physicalInputCount (parameterM D j) (parameterW A j) =
        parameterLength A D j ∧
      logicalOutputCount (parameterM D j) (parameterW A j) =
        parameterDimension A D j ∧
      codeDistance (parameterR D j) (parameterW A j) =
        parameterDistance A D j := by
  constructor
  · rw [physicalInputCount_eq_binomialTail]
    rfl
  constructor
  · rw [logicalOutputCount_eq_binomialUpTo]
    rfl
  · rfl
private theorem selected_pooling_rate_exists
    {w r m : Nat} (_h : Admissible w r m) :
    ∃ epsilon : HH18NoisyInput.DiagonalErrorRate,
      0 < epsilon.1 ∧ decodedRetryPoolInitialPoolingDomain w r m epsilon := by
  let scale := routedDepthIterationScale w r m
  let outputs := (logicalOutputCount m w : ℝ)
  let rate : ℝ := 1 / (128 * scale * outputs)
  have hscale : 0 < scale := by
    dsimp [scale]
    exact routedDepthIterationScale_pos w r m
  have houtputs : 0 < outputs := by
    dsimp [outputs]
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hrate : 0 < rate := by
    dsimp [rate]
    exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) hscale) houtputs)
  have hrate_le_half : rate ≤ 1 / 2 := by
    have hden : (2 : ℝ) ≤ 128 * scale * outputs := by
      have hscale_one : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        exact routedDepthIterationScale_one_le w r m
      have houtputs_one : (1 : ℝ) ≤ outputs := by
        change (1 : ℝ) ≤ (logicalOutputCount m w : ℝ)
        exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
      nlinarith
    exact (one_div_le_one_div_of_le (by norm_num) hden).trans_eq (by norm_num)
  let epsilon : HH18NoisyInput.DiagonalErrorRate := ⟨rate, hrate.le, hrate_le_half⟩
  refine ⟨epsilon, hrate, ?_⟩
  change scale * rate ≤ 1 / (64 * outputs)
  have hproduct : scale * rate = 1 / (128 * outputs) := by
    dsimp [rate]
    field_simp [hscale.ne', houtputs.ne']
  rw [hproduct]
  apply one_div_le_one_div_of_le
  · exact mul_pos (by norm_num) houtputs
  · nlinarith
private theorem selected_target_tendsto_zero
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (_hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    Tendsto (fun depth : Nat =>
      routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0) := by
  let base : ℝ := routedDepthIterationScale w r m * epsilon.1
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    exact mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hbase1 : base < 1 := by
    dsimp [base]
    exact (decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
      epsilon hpool).trans_lt (by norm_num)
  have hpow : Tendsto (fun t : Nat => base ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have hdistance : 1 < codeDistance r w := by
    exact_mod_cast codeDistance_two_le h
  have hgrowth : Tendsto (fun depth : Nat => codeDistance r w ^ (depth + 1))
      atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt hdistance).comp
      (tendsto_add_atTop_nat 1)
  have hport := hpow.comp hgrowth
  simp only [routedDepthScheduleTargetError, base] at hport ⊢
  exact hport
private theorem selected_actual_output_tendsto_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (rhoUnit : DensityOperator
      (QEC.Semantics.FiniteInstrument.tensorPowerCarrier (PhysicalRegister m w) 0))
    (htarget : Tendsto (fun depth : Nat =>
      routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0)) :
    Tendsto (fun depth : Nat =>
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htarget
    (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError_nonneg
      h hdegree epsilon depth rhoUnit)
    (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit)
end QEC.Distillation.HH18
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18
open Coding
open Coding.PuncturedReedMuller
open Filter Topology
open Semantics
open Semantics.FiniteInstrument
open QEC.Distillation.HH18PuncturedReedMuller
open HH18SublogarithmicEntropy
open HH18Parameterized
namespace QEC.Distillation.HH18
theorem _root_.solution (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
      0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
      let r := parameterR D j
      let w := parameterW A j
      let m := parameterM D j
      let n := parameterLength A D j
      let k := parameterDimension A D j
      let d := parameterDistance A D j
      ∃ h : Admissible w r m,
        m = 3 * r + 1 ∧ 0 ≤ 2 * w ∧ 2 * w < 2 * r ∧ 2 * r < m ∧
        (w : ℚ) = 3 * (r : ℚ) * q ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) = n ∧
        Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w) - Dimension (xCode w r m) -
            Dimension (zCode w r m) = k ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier = 2 ^ k ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h) d ∧
        (encodedCode h).ImplementsLogicalGate (physicalT w m) (logicalTInv w m) ∧
        (encodedCode h).ImplementsLogicalGate (physicalTInv w m) (logicalT w m) ∧
        hh18GammaInf ≤ hh18Gamma p0R ∧ hh18Gamma p0R < (339 / 500 : ℝ) ∧
        (339 / 500 : ℝ) < 1 ∧
        ∃ epsilon : HH18NoisyInput.DiagonalErrorRate,
          0 < epsilon.1 ∧
          ∃ hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon,
          ∃ gamma : ℝ,
            gamma = routedDepthScheduleGamma w r m ∧
            gamma = Real.log ((n : ℝ) / k) / Real.log d ∧
            |gamma - hh18GammaInf| < eta ∧ gamma < 1 ∧
          ∃ coefficient : ℝ,
            coefficient = decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon ∧
            0 < coefficient ∧ 0 ≤ coefficient ∧
            (∀ depth : Nat,
              PolylogarithmicOverhead
                (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity)
                gamma coefficient ∧
              decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity =
                DistillationProtocolFamily.successfulOutputCost
                  (decodedRetryPoolPhysicalExactBatchProtocolFamily h
                  (selected_transversal_t_degree A D j) epsilon
                  hpool depth
                  decodedRetryPoolTensorUnitDensity) PUnit.unit) ∧
            Tendsto (fun depth : Nat =>
              routedDepthScheduleTargetError w r m epsilon (depth + 1)) atTop (𝓝 0) ∧
            Tendsto (fun depth : Nat =>
              decodedRetryPoolPhysicalExactBatchActualOutputError h
                (selected_transversal_t_degree A D j) epsilon depth
                decodedRetryPoolTensorUnitDensity) atTop (𝓝 0) := by
  rcases exists_finite_subunit_gamma_selector eta heta with
    ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, hselected⟩
  dsimp at hselected
  rcases hselected with ⟨h, hslope, hgamma, hclose, _, hsubunit⟩
  rcases parameter_sequence_admissible A D j hA hD hwindow hj with
    ⟨hm, hslopeSequence, hadmissible⟩
  have hslope' : (parameterW A j : ℚ) =
      3 * (parameterR D j : ℚ) * q := by
    rw [hslopeSequence, hq]
  have hcounts := selected_physical_counts A D j
  rcases hcounts with ⟨hn, hk, hd⟩
  have hgammaSchedule :
      routedDepthScheduleGamma (parameterW A j) (parameterR D j) (parameterM D j) =
        Real.log ((parameterLength A D j : ℝ) / parameterDimension A D j) /
          Real.log (parameterDistance A D j) := by
    unfold routedDepthScheduleGamma
    rw [hn, hk, hd]
  have hp0lower : hh18GammaInf ≤ hh18Gamma p0R := by
    rw [hh18GammaInf]
    exact csInf_le hh18GammaSet_bddBelow ⟨p0R, p0_mem_parameterInterval, rfl⟩
  rcases selected_pooling_rate_exists h with ⟨epsilon, hepsilon, hpool⟩
  let rhoUnit : DensityOperator
      (QEC.Semantics.FiniteInstrument.tensorPowerCarrier
        (PhysicalRegister (parameterM D j) (parameterW A j)) 0) :=
    decodedRetryPoolTensorUnitDensity
  let coefficient := decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool).le
  have htarget := selected_target_tendsto_zero h epsilon hepsilon hpool
  have hactual := selected_actual_output_tendsto_zero
    h (selected_transversal_t_degree A D j) epsilon hpool rhoUnit htarget
  refine ⟨q, A, D, j, hqL, hqU, hA, hD, hwindow, hj, hq, ?_⟩
  dsimp
  refine ⟨h, hm, h.1, h.2.1, h.2.2, hslope', ?_, ?_, ?_, ?_, ?_, ?_,
    hp0lower, hh18Gamma_p0_lt_339_div_500, by norm_num, epsilon, hepsilon,
    hpool, routedDepthScheduleGamma (parameterW A j) (parameterR D j) (parameterM D j),
    rfl, hgammaSchedule, ?_, ?_, coefficient, rfl, ?_, hcoefficient, ?_, htarget,
    hactual⟩
  · exact (cssParameters h).1
  · exact (cssParameters h).2.1
  · exact (cssParameters h).2.2.1
  · exact (cssParameters h).2.2.2
  · exact HH18PuncturedReedMuller.physicalT_implements_logicalTInv
      h (selected_transversal_t_degree A D j)
  · exact HH18PuncturedReedMuller.physicalTInv_implements_logicalT
      h (selected_transversal_t_degree A D j)
  · rw [hgammaSchedule, ← hgamma]
    exact hclose
  · rw [hgammaSchedule, ← hgamma]
    exact hsubunit
  · dsimp [coefficient]
    exact decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool
  · intro depth
    constructor
    · dsimp [coefficient, rhoUnit]
      exact decodedRetryPoolPhysicalExactBatchProtocolFamily_polylogarithmicOverhead
        h (selected_transversal_t_degree A D j) epsilon hepsilon hpool depth
          decodedRetryPoolTensorUnitDensity
    · exact decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
        h (selected_transversal_t_degree A D j) epsilon hpool depth
          decodedRetryPoolTensorUnitDensity
end QEC.Distillation.HH18
