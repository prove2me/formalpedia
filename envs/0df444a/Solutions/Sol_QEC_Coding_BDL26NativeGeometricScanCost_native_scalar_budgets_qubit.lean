-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricScanCost.native_scalar_budgets_qubit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:21:23.876413+00:00
-- url     : https://prove2.me/submissions/2eab8631-12c0-4b0c-a415-2d087ee58fe1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricScanCost_native_scan_budget_closed_le
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_x
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_z
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_zero
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_zero
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_succ
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_self
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_last
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_totalStageCost_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_setupExponent_value
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_setup_cost
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_native_length_bound
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_transferTotal_zero
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_nextState_qubit_card_lower
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qDoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seedPoint_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_bottom
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_diagonal
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_left
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_right
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_top
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_lower_last_normalized
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_interior
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_last
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_two_complement_val
import Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_upper_last_normalized
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_eval_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_reads_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_work_rename
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_blendCode_reads
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_blendCode_work
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_totalMaterializationCost_zero
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ0SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4DoubleCylinderVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4StarVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionEdge_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_baseQ4SubdivisionVertex_card
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_CSSGibbs_badProjector_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_one
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_sign
import Theorems.Thm_QEC_Coding_CSSGibbs_bitOutcome_zero
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssX
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssZ
import Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_row
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_square
import Theorems.Thm_QEC_Coding_CSSGibbs_realizableEmbedding_apply
import Theorems.Thm_QEC_Coding_CSSGibbs_row_adjoint
import Theorems.Thm_QEC_Coding_CSSGibbs_syndromeOutcome_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_one
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_zero
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_x
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_y
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_z
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.check_hermitian
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport
attribute [local simp] QEC.Coding.BDL26CountableEmbeddingExperiment.levelMap_zero
attribute [local simp] QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_zero
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_succ
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.history_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_self
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_last
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.totalStageCost_zero
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26IncomingRowsExecution.rowTotalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.totalCost_zero
attribute [local simp] QEC.Coding.BDL26PaidRowsComposition.transferTotal_zero
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.centerExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomSeedEmbedding.seedPoint_eq_zero
attribute [local simp] QEC.Coding.BDL26RandomSeedEmbedding.seed_physical_zero
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_bottom
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_diagonal
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_left
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_right
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_top
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.lower_last_normalized
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_interior
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_last
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.two_complement_val
attribute [local simp] QEC.Coding.BDL26ReplacementEmbedding.upper_last_normalized
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.eval_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.reads_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.PointCode.work_rename
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.blendCode_reads
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.blendCode_work
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_zero
attribute [local simp] QEC.Coding.BDL26ReplacementMaterialization.totalMaterializationCost_zero
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
attribute [local simp] QEC.Coding.BDL26ReplacementSupport.rxQOutgoing_nonincident
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionVertex_card
attribute [local simp] QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
attribute [local simp] QEC.Coding.CSSGibbs.badProjector_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_one
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_sign
attribute [local simp] QEC.Coding.CSSGibbs.bitOutcome_zero
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_cssX
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_cssZ
attribute [local simp] QEC.Coding.CSSGibbs.hermitian_row
attribute [local simp] QEC.Coding.CSSGibbs.projector_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.projector_square
attribute [local simp] QEC.Coding.CSSGibbs.realizableEmbedding_apply
attribute [local simp] QEC.Coding.CSSGibbs.row_adjoint
attribute [local simp] QEC.Coding.CSSGibbs.syndromeOutcome_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_table
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_table
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


section
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricScanCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26NativeKeyExecutionBridge
open scoped Classical
private theorem closedScanBudget_mono {a b z a' b' z' : ℕ} (K : ℕ)
    (ha : a ≤ a') (hb : b ≤ b') (hz : z ≤ z') :
    closedScanBudget a b K z ≤ closedScanBudget a' b' K z' := by
  dsimp only [closedScanBudget]
  gcongr
private theorem closedScanBudget_diagonal (x K : ℕ) (hx : 1 ≤ x) :
    closedScanBudget x x K x ≤ scanPolynomialConstant K*x^8 := by
  let g := gridBudget K
  let h := (2*K+1)^3
  have hp (j : ℕ) (hj : j ≤ 8) : x^j ≤ x^8 :=
    Nat.pow_le_pow_right (by omega) hj
  have h0 : 1 ≤ x^8 := by simpa only [pow_zero] using hp 0 (by decide)
  have h1 : x ≤ x^8 := by simpa only [pow_one] using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have hconstant : 685 ≤ 685*x^8 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 685 h0
  calc
    _ = 159*x^8+(900*h+9010)*x^6+(585*h+5911)*x^5+
        (g+3*h*K+800740*h+35211)*x^4+4099*x^3+4163*x^2+2299*x+685 := by
      dsimp only [closedScanBudget,g,h] <;> ring
    _ ≤ 159*x^8+(900*h+9010)*x^8+(585*h+5911)*x^8+
        (g+3*h*K+800740*h+35211)*x^8+4099*x^8+4163*x^8+2299*x^8+685*x^8 := by
      gcongr <;> assumption
    _ = _ := by dsimp only [scanPolynomialConstant,g,h] <;> ring
private theorem depth_le_qubits (S : OddScale) (n : ℕ) :
    n+1 ≤ Fintype.card (Presentation S n).Q := by
  have hp : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; nlinarith
  have hq : 5*2^n ≤ Fintype.card (Presentation S n).Q :=
    BDL26QuantitativeBounds.state_qubit_card_lower S n
  omega
private theorem qubits_mono (S : OddScale) :
    Monotone (fun n => Fintype.card (Presentation S n).Q) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := BDL26QuantitativeBounds.nextState_qubit_card_lower S n
    (BDL26DecodingGraph.state S n)
  change 2*Fintype.card (Presentation S n).Q ≤ Fintype.card (Presentation S (n+1)).Q at h
  omega
private theorem scale_le_positive_qubits (S : OddScale) (n : ℕ) (hn : 1 ≤ n) :
    S.ell ≤ Fintype.card (Presentation S n).Q := by
  let P := BDL26DecodingGraph.baseState.presentation
  let q : P.Q := (0 : BDL26FiniteAlternatingCore.BaseQubit)
  let f : BDL26TannerLocalRegularity.QDoubleCylinderVertex P q S →
      BDL26RXLocalReplacement.RX1 P S := fun v => Sum.inr ⟨q,v⟩
  have hi : Function.Injective f := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
  have hc := Fintype.card_le_of_injective f hi
  rw [BDL26QuantitativeBounds.qDoubleCylinderVertex_card] at hc
  have he : Fintype.card (BDL26TannerLocalRegularity.QStarEdge P q)=1 := by decide
  rw [he] at hc
  have hs := S.two_half_add_one
  have hfirst : S.ell ≤ Fintype.card (Presentation S 1).Q := by
    change S.ell ≤ Fintype.card (BDL26RXLocalReplacement.RX1 P S)
    omega
  exact hfirst.trans (qubits_mono S hn)
private theorem radius_power_bounds (s q d r : ℕ)
    (hs : s ≤ q) (hd : d ≤ q) (hr : r=s+130*q+2) :
    1 ≤ (132*(q+1))^221 ∧
    d*r^220 ≤ (132*(q+1))^221 ∧
    d*r^15 ≤ (132*(q+1))^221 := by
  let R : ℕ := 132*(q+1)
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hdn : d ≤ R := by dsimp only [R]; omega
  have hrn : r ≤ R := by dsimp only [R]; omega
  refine ⟨one_le_pow₀ hR,?_,?_⟩
  · calc
      d*r^220 ≤ R*R^220 := Nat.mul_le_mul hdn (Nat.pow_le_pow_left hrn 220)
      _ = R^221 := (pow_succ' R 220).symm
  · calc
      d*r^15 ≤ R*R^15 := Nat.mul_le_mul hdn (Nat.pow_le_pow_left hrn 15)
      _ = R^16 := (pow_succ' R 15).symm
      _ ≤ R^221 := Nat.pow_le_pow_right (by omega) (by decide)
private theorem incoming_scalar_envelope (u v x : ℕ)
    (hu : u ≤ x) (hv : v ≤ x) (hx : 1 ≤ x) :
    u+2*v^2+12*v+4 ≤ 19*x^2 := by
  have hx2 : x ≤ x^2 := by nlinarith
  have h1 : 1 ≤ x^2 := by nlinarith
  calc
    u+2*v^2+12*v+4 ≤ x+2*x^2+12*x+4 := by gcongr
    _ ≤ 19*x^2 := by nlinarith
private theorem scalar_budgets_from_power_bounds (S : OddScale) (n K x : ℕ)
    (hx : 1 ≤ x)
    (ha : (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220 ≤ x)
    (hb : (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 ≤ x) :
    incomingBudget S n ≤ 19*x^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*x^8 ∧
    SR.count S n ≤ x := by
  have hv : SR.count S n ≤ x :=
    (BDL26NativeStateRows.native_length_bound S n).trans hb
  have hs := BDL26NativePresentationGenerator.setup_cost S n
  rw [BDL26NativePresentationGenerator.setupExponent_value] at hs
  have hsetup := hs.trans ha
  refine ⟨?_,?_,hv⟩
  · exact incoming_scalar_envelope
      (BDL26NativePresentationGenerator.setupQ S n).2 (SR.count S n) x hsetup hv hx
  · exact (native_scan_budget_closed_le S n K (SR.count S n)).trans
      ((closedScanBudget_mono K ha hb hv).trans (closedScanBudget_diagonal x K hx))
private theorem scalar_budgets_of_scale_le (S : OddScale) (n K : ℕ)
    (hscale : S.ell ≤ Fintype.card (Presentation S n).Q) :
    incomingBudget S n ≤ 19*(qubitRadius S n)^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*(qubitRadius S n)^8 ∧
    SR.count S n ≤ qubitRadius S n := by
  have h := radius_power_bounds S.ell (Fintype.card (Presentation S n).Q)
    (n+1) (BDL26NativePresentationGenerator.inputRadius S n)
    hscale (depth_le_qubits S n) rfl
  exact scalar_budgets_from_power_bounds S n K (qubitRadius S n) h.1 h.2.1 h.2.2
private theorem seed_setup_programs_eq (S T : OddScale) :
    BDL26NativePresentationGenerator.setupQ S 0=
      BDL26NativePresentationGenerator.setupQ T 0 ∧
    BDL26NativePresentationGenerator.allocatedRecords S 0=
      BDL26NativePresentationGenerator.allocatedRecords T 0 := by
  have hh : BDL26NativePresentationGenerator.historyQ S 0=
      BDL26NativePresentationGenerator.historyQ T 0 := by
    change ([BDL26NativePresentationGenerator.seedFrameQ.1],
      BDL26NativePresentationGenerator.seedFrameQ.2+1)=_
    exact Eq.refl _
  have ha : BDL26NativePresentationGenerator.Allocation.historyQ S 0=
      BDL26NativePresentationGenerator.Allocation.historyQ T 0 := by
    change ([BDL26NativePresentationGenerator.Allocation.seedFrameQ.1],
      BDL26NativePresentationGenerator.Allocation.seedFrameQ.2+1)=_
    exact Eq.refl _
  constructor
  · simp only [BDL26NativePresentationGenerator.setupQ,
      BDL26NativePresentationGenerator.runQ,
      BDL26NativePresentationGenerator.generateQ,hh]
  · simp only [BDL26NativePresentationGenerator.allocatedRecords,
      BDL26NativePresentationGenerator.Allocation.setupQ,
      BDL26NativePresentationGenerator.Allocation.runQ,
      BDL26NativePresentationGenerator.Allocation.generateQ,ha]
private theorem component_costs_eq_of_setup_eq (S T : OddScale) (n m : ℕ)
    (hs : BDL26NativePresentationGenerator.setupQ S n=
      BDL26NativePresentationGenerator.setupQ T m)
    (ha : BDL26NativePresentationGenerator.allocatedRecords S n=
      BDL26NativePresentationGenerator.allocatedRecords T m) :
    (MC.masterCandidatesQ S n).operations=(MC.masterCandidatesQ T m).operations ∧
    (MD.atlasQ S n).operations=(MD.atlasQ T m).operations ∧
    (BDL26NativeTriangleColors.colorsQ S n).operations=
      (BDL26NativeTriangleColors.colorsQ T m).operations := by
  -- Nat-valued observations bind the generated carrier inside the lambda.
  -- Congruence therefore transports its vertex list and Fin carrier together.
  let atlasCost := fun generated :
      BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput =>
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    generated.2+out.operations+2
  let colorCost := fun generated :
      BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput =>
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    let rows := @BDL26NativeTriangleColors.colorRowsQ
      (Fin generated.1.data.vertices.length)
      (instDecidableEqFin generated.1.data.vertices.length) out.value
    (generated.2+out.operations+2)+rows.operations+2
  -- This proof-local observation is the delta expansion of the original
  -- master/candidate/query/atlas constructors. Every paid branch and field is
  -- retained; quadruples and all list/lookup programs remain unexpanded.
  let masterCost := fun input :
      (BDL26NativePresentationGenerator.Query BDL26NativePresentationGenerator.SetupOutput) × ℕ =>
    let generated := input.1
    let allocated := input.2
    let out := BDL26NativeSupportMetadata.atlasRowsQ generated.1.data.frame
      generated.1.data.vertices generated.1.triangles
    let atlas : BDL26NativeStateRows.Run
        (List (MD.Code × Option (BDL26NativeSupportMetadata.Triple
          (Fin generated.1.data.vertices.length)))) :=
      ⟨out.value,generated.2+out.operations+2,allocated+out.allocations+1⟩
    let query : MD.FourCodes → BDL26NativeStateRows.Run
        (Option (List (Fin generated.1.data.vertices.length))) := fun codes =>
      let a := BDL26NativeSupportMetadata.atlasReadQ codes.first atlas.value
      let b := BDL26NativeSupportMetadata.atlasReadQ codes.second atlas.value
      let c := BDL26NativeSupportMetadata.atlasReadQ codes.third atlas.value
      let d := BDL26NativeSupportMetadata.atlasReadQ codes.fourth atlas.value
      match a.value,b.value,c.value,d.value with
      | some x,some y,some z,some w =>
          let dedup := @BDL26NativeSupportMetadata.dedupQ
            (Fin generated.1.data.vertices.length)
            (instDecidableEqFin generated.1.data.vertices.length)
            (BDL26NativeSupportMetadata.twelve x y z w)
          ⟨some dedup.value,
            atlas.operations+a.operations+b.operations+c.operations+d.operations+
              dedup.operations+30,
            atlas.allocations+dedup.allocations+13⟩
      | _,_,_,_ =>
          ⟨none,atlas.operations+a.operations+b.operations+c.operations+d.operations+6,
            atlas.allocations⟩
    let candidate : MD.Code → MD.Code → MD.Code → MD.Code →
        BDL26NativeStateRows.Run
          (MD.FourCodes × Option (List (Fin generated.1.data.vertices.length))) := fun a b c d =>
      let ca := BDL26NativeMasterCandidates.copyCodeQ a
      let cb := BDL26NativeMasterCandidates.copyCodeQ b
      let cc := BDL26NativeMasterCandidates.copyCodeQ c
      let cd := BDL26NativeMasterCandidates.copyCodeQ d
      let codes := BDL26NativeMasterCandidates.pack ca.value cb.value cc.value cd.value
      let queried := query codes
      ⟨(codes,queried.value),ca.operations+cb.operations+cc.operations+cd.operations+
        queried.operations+5+3+8,
        ca.allocations+cb.allocations+cc.allocations+cd.allocations+queried.allocations+1+1⟩
    let rows := BDL26NativeMasterCandidates.quadruplesQ candidate generated.1.triangles
    generated.2+rows.operations+2
  -- Here k is a free variable, so the original history/list programs stay
  -- symbolic while definitional equality checks only their outer constructors.
  have hmaster (U : OddScale) (k : ℕ) :
      (MC.masterCandidatesQ U k).operations=
        masterCost (BDL26NativePresentationGenerator.setupQ U k,
          BDL26NativePresentationGenerator.allocatedRecords U k) := by
    dsimp only [BDL26NativeMasterCandidates.masterCandidatesQ,masterCost]
    apply congrArg (fun f : MD.Code → MD.Code → MD.Code → MD.Code →
        BDL26NativeStateRows.Run (MD.FourCodes × Option (List (SR.Index U k))) =>
      (BDL26NativePresentationGenerator.setupQ U k).2+
        (BDL26NativeMasterCandidates.quadruplesQ f
          (BDL26NativePresentationGenerator.setupQ U k).1.triangles).operations+2)
    funext a b c d
    let codes : MD.FourCodes := BDL26NativeMasterCandidates.pack
      (BDL26NativeMasterCandidates.copyCodeQ a).value
      (BDL26NativeMasterCandidates.copyCodeQ b).value
      (BDL26NativeMasterCandidates.copyCodeQ c).value
      (BDL26NativeMasterCandidates.copyCodeQ d).value
    cases h₁ : (BDL26NativeSupportMetadata.atlasReadQ codes.first
        (MD.atlasQ U k).value).value <;>
      cases h₂ : (BDL26NativeSupportMetadata.atlasReadQ codes.second
        (MD.atlasQ U k).value).value <;>
      cases h₃ : (BDL26NativeSupportMetadata.atlasReadQ codes.third
        (MD.atlasQ U k).value).value <;>
      cases h₄ : (BDL26NativeSupportMetadata.atlasReadQ codes.fourth
        (MD.atlasQ U k).value).value
    all_goals
      dsimp only [codes,BDL26NativeSupportMetadata.atlasQ] at h₁ h₂ h₃ h₄
      simp only [BDL26NativeMasterCandidates.candidateQ,
        BDL26NativeSupportMetadata.queryQ,BDL26NativeSupportMetadata.atlasQ,
        h₁,h₂,h₃,h₄] <;> congr <;> exact Subsingleton.elim _ _
  have hatlas (U : OddScale) (k : ℕ) :
      (MD.atlasQ U k).operations=
        atlasCost (BDL26NativePresentationGenerator.setupQ U k) := by
    rfl
  have hcolors (U : OddScale) (k : ℕ) :
      (BDL26NativeTriangleColors.colorsQ U k).operations=
        colorCost (BDL26NativePresentationGenerator.setupQ U k) := by
    rfl
  refine ⟨?_,?_,?_⟩
  · exact (hmaster S n).trans
      ((congrArg masterCost (Prod.ext hs ha)).trans (hmaster T m).symm)
  · exact (hatlas S n).trans ((congrArg atlasCost hs).trans (hatlas T m).symm)
  · exact (hcolors S n).trans ((congrArg colorCost hs).trans (hcolors T m).symm)
private theorem seed_component_costs_eq (S T : OddScale) :
    (MC.masterCandidatesQ S 0).operations=(MC.masterCandidatesQ T 0).operations ∧
    (MD.atlasQ S 0).operations=(MD.atlasQ T 0).operations ∧
    (BDL26NativeTriangleColors.colorsQ S 0).operations=
      (BDL26NativeTriangleColors.colorsQ T 0).operations := by
  rcases seed_setup_programs_eq S T with ⟨hs,ha⟩
  exact component_costs_eq_of_setup_eq S T 0 0 hs ha
private theorem seed_budget_transport (S T : OddScale) (K z : ℕ) :
    incomingBudget S 0=incomingBudget T 0 ∧
    scanBudget S 0 K z=scanBudget T 0 K z ∧
    SR.count S 0=SR.count T 0 ∧
    qubitRadius S 0=qubitRadius T 0 := by
  have hs := (seed_setup_programs_eq S T).1
  have hc := seed_component_costs_eq S T
  have hv : SR.count S 0=SR.count T 0 := by
    exact congrArg (fun generated => generated.1.data.vertices.length) hs
  have ht : triangleCount S 0=triangleCount T 0 := by
    exact congrArg (fun generated => generated.1.triangles.length) hs
  have hi : incomingBudget S 0=incomingBudget T 0 := by
    simp only [incomingBudget,BDL26NativeStateRows.count,hs]
  refine ⟨hi,?_,hv,?_⟩
  · simp only [scanBudget,preprocessingBudget,masterCount,eligibilityBudget,
      pairBudget,colorBudget,triangleBudget,atlasReadBudget,pointBudget,
      centerBudget,queryBudget,hc.1,hc.2.1,hc.2.2,ht,hi,hv]
  · change (132*(Fintype.card BDL26DecodingGraph.baseState.presentation.Q+1))^221=
      (132*(Fintype.card BDL26DecodingGraph.baseState.presentation.Q+1))^221
    exact Eq.refl _
end QEC.Coding.BDL26NativeGeometricScanCost
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricScanCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26NativeKeyExecutionBridge
open scoped Classical
namespace QEC.Coding.BDL26NativeGeometricScanCost
theorem _root_.solution (S : OddScale) (n K : ℕ) :
    incomingBudget S n ≤ 19*(qubitRadius S n)^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*(qubitRadius S n)^8 ∧
    SR.count S n ≤ qubitRadius S n := by
  by_cases hn : n=0
  · subst n
    let S0 : OddScale := ⟨3,rfl,by decide⟩
    have hq : 5 ≤ Fintype.card (Presentation S0 0).Q := by
      simpa only [pow_zero,Nat.mul_one] using
        BDL26QuantitativeBounds.state_qubit_card_lower S0 0
    have h0 : S0.ell ≤ Fintype.card (Presentation S0 0).Q :=
      (show 3 ≤ 5 by decide).trans hq
    have ht := seed_budget_transport S S0 K (SR.count S 0)
    rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    exact scalar_budgets_of_scale_le S0 0 K h0
  · exact scalar_budgets_of_scale_le S n K
      (scale_le_positive_qubits S n (by omega))
end QEC.Coding.BDL26NativeGeometricScanCost
