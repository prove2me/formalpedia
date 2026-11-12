-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:55:07.838538+00:00
-- url     : https://prove2.me/submissions/34e9cf37-f089-46af-9999-58f0b06bdb06

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis
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
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegisterTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorReindexChannel_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
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
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
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
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegisterTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoRouting_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator
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
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
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


attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerBitstringEquiv_symm_at

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w : Nat) (port : LogicalSite m w)
    (rho : DensityOperator (LogicalRegister m w)) :
    (decodedRetryPoolQubitRegisterCoordinateChannel
        (LogicalSite m w) port).mapDensity rho =
      (selectedLogicalPortTransport m w port).conjDensity
        ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
          rho) := by
  apply DensityOperator.ext_toOperator
  simp only [QuantumChannel.mapDensity_toOperator,
    UnitaryTransport.conjDensity_toOperator]
  let sourceBasis := EuclideanSpace.basisFun
    (Bitstring (LogicalSite m w)) Complex
  let selectedChannel : QuantumChannel (LogicalRegister m w) QubitSpace :=
    QuantumChannel.comp
      (QuantumChannel.unitaryConj (selectedLogicalPortTransport m w port))
      (selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister
  have hselectedRankOne (left right : Bitstring (LogicalSite m w)) :
      selectedChannel
          (InnerProductSpace.rankOne Complex (sourceBasis left)
            (sourceBasis right)).toLinearMap =
        inner Complex
            (EuclideanSpace.basisFun
              (Bitstring
                (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
              Complex
              ((selectedLogicalPortSubsystem m w port).splitBitstring right).2)
            (EuclideanSpace.basisFun
              (Bitstring
                (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
              Complex
              ((selectedLogicalPortSubsystem m w port).splitBitstring left).2) •
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Fin 2) Complex (left port))
            (EuclideanSpace.basisFun (Fin 2) Complex (right port))).toLinearMap := by
    simp only [selectedChannel, FiniteSubsystem.selectedPartialTraceFromRegister,
      QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
    rw [QuditSubsystem.conjOperator_rankOne,
      FiniteSubsystem.registerFactorization_apply_basis,
      FiniteSubsystem.registerFactorization_apply_basis]
    rw [FiniteSubsystem.selectedPartialTrace_toLinearMap,
      QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [← UnitaryTransport.conjOperatorLinearMap_apply]
    rw [(selectedLogicalPortTransport m w port).conjOperatorLinearMap.map_smul]
    simp only [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [QuditSubsystem.conjOperator_rankOne]
    rw [selectedLogicalPortTransport_apply_basis,
      selectedLogicalPortTransport_apply_basis]
    rfl
  have hmaps :
      (decodedRetryPoolQubitRegisterCoordinateChannel
        (LogicalSite m w) port).toLinearMap = selectedChannel.toLinearMap := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis sourceBasis
    intro left right
    rw [decodedRetryPoolQubitRegisterCoordinateChannel_rankOne_basis]
    rw [hselectedRankOne]
    refine congrArg (fun scalar : Complex => scalar •
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (left port))
        (EuclideanSpace.basisFun (Fin 2) Complex (right port))).toLinearMap) ?_
    by_cases hcomplement :
        ((selectedLogicalPortSubsystem m w port).splitBitstring right).2 =
          ((selectedLogicalPortSubsystem m w port).splitBitstring left).2
    · have hfactor (coordinate : Fin (Fintype.card (LogicalSite m w))) :
          (if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 1 := by
        by_cases hcoordinate : coordinate = Fintype.equivFin (LogicalSite m w) port
        · simp [hcoordinate]
        · have hsite :
              (Fintype.equivFin (LogicalSite m w)).symm coordinate ≠ port := by
            intro heq
            apply hcoordinate
            rw [← heq, Equiv.apply_symm_apply]
          let complement :
              (selectedLogicalPortSubsystem m w port).ComplementCoordinates :=
            ⟨(Fintype.equivFin (LogicalSite m w)).symm coordinate, by
              simpa [selectedLogicalPortSubsystem] using hsite⟩
          have hbit := congrFun hcomplement complement
          simp only [FiniteSubsystem.splitBitstring] at hbit
          have hbit' :
              right ((Fintype.equivFin (LogicalSite m w)).symm coordinate) =
                left ((Fintype.equivFin (LogicalSite m w)).symm coordinate) := by
            exact hbit
          rw [if_neg hcoordinate, hbit']
          rw [(EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
          simp
      rw [Fintype.prod_eq_one _ hfactor]
      rw [(EuclideanSpace.basisFun
        (Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
        Complex).inner_eq_ite]
      rw [if_pos hcomplement]
    · have hexists : ∃ complement :
          (selectedLogicalPortSubsystem m w port).ComplementCoordinates,
          ((selectedLogicalPortSubsystem m w port).splitBitstring right).2 complement ≠
            ((selectedLogicalPortSubsystem m w port).splitBitstring left).2 complement := by
        by_contra hnone
        simp only [not_exists, not_not] at hnone
        apply hcomplement
        funext complement
        exact hnone complement
      obtain ⟨complement, hbit⟩ := hexists
      let coordinate : Fin (Fintype.card (LogicalSite m w)) :=
        Fintype.equivFin (LogicalSite m w) complement.1
      have hcoordinate :
          coordinate ≠ Fintype.equivFin (LogicalSite m w) port := by
        intro heq
        have hsite : (complement : LogicalSite m w) = port :=
          (Fintype.equivFin (LogicalSite m w)).injective heq
        exact complement.2 (by simp [selectedLogicalPortSubsystem, hsite])
      have hzero :
          (if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 0 := by
        simp only [hcoordinate, if_false, coordinate, Equiv.symm_apply_apply,
          (EuclideanSpace.basisFun (Fin 2) Complex).inner_eq_ite]
        simp only [FiniteSubsystem.splitBitstring] at hbit
        simp [hbit]
      have hproduct :
          (∏ coordinate : Fin (Fintype.card (LogicalSite m w)),
            if coordinate = Fintype.equivFin (LogicalSite m w) port then 1
            else inner Complex
              (EuclideanSpace.basisFun (Fin 2) Complex
                (right ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))
              (EuclideanSpace.basisFun (Fin 2) Complex
                (left ((Fintype.equivFin (LogicalSite m w)).symm coordinate)))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ coordinate) hzero
      rw [hproduct]
      rw [(EuclideanSpace.basisFun
        (Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates)
        Complex).inner_eq_ite]
      rw [if_neg hcomplement]
  change (decodedRetryPoolQubitRegisterCoordinateChannel
      (LogicalSite m w) port).toLinearMap rho.toOperator =
    selectedChannel.toLinearMap rho.toOperator
  exact LinearMap.congr_fun hmaps rho.toOperator
end QEC.Distillation.HH18Parameterized
