-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecutionCost.measurable_nativeOperationCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:17:23.886345+00:00
-- url     : https://prove2.me/submissions/a092f814-2b36-4d3b-860c-5dc616442dff

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_stopping_refinement
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
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_haltTime_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_halts_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_assignment
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_point_actual
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_length
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_cost
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_order
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_value
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_labels
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_zero
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_transferTotal_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAllQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAnyQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_scanQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_triangleQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_cost
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
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_halts
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_counters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_haltTime
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
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
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
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
namespace QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
private theorem initialized_length (S : OddScale) (n : ℕ) (T : NativeTable S n) :
    (SR.initializeQ S n T).value.length=SR.count S n := by
  simp only [SR.initialize_value,SR.rowsFor,List.length_map,
    BDL26NativeStateRows.indices_length]
private theorem refresh_length (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (U : List (SR.Index S n)) (R : SR.Rows (SR.Index S n)) :
    (SR.refreshQ T U R).value.length=R.length := by
  have h := congrArg List.length (BDL26NativeStateRows.refresh_labels T U R)
  simpa only [List.length_map] using h
private theorem prefix_operations_succ (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T (m+1)).operations =
      (prefixQ S n J hr lambda K T m).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
        (SR.refreshQ T (chosenSupport S n J r
          (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
          (prefixQ S n J hr lambda K T m).value.rows).operations+
        (BDL26NativeMasterCandidates.appendQ
          (prefixQ S n J hr lambda K T m).value.trace
          [(scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1]).operations+4 := by
  rfl
private theorem prefix_lengths (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows.length=SR.count S n ∧
      (prefixQ S n J hr lambda K T m).value.trace.length=m := by
  induction m with
  | zero => exact ⟨initialized_length S n T,rfl⟩
  | succ m ih =>
      constructor
      · exact (refresh_length S n T _ _).trans ih.1
      · change (BDL26NativeMasterCandidates.appendQ
          (prefixQ S n J hr lambda K T m).value.trace [_]).value.length=m+1
        rw [(BDL26NativeMasterCandidates.append_spec _ _).1,
          List.length_append,ih.2]
        rfl
private theorem read_cost_labels {A : Type*} [DecidableEq A] (a : A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.readQ a R).operations=readLabelCost a (R.map Prod.fst) := by
  induction R with
  | nil => rfl
  | cons row R ih =>
      by_cases h : row.1=a <;>
        simp only [BDL26NativeStateRows.readQ,List.map_cons,readLabelCost,h,if_true,if_false,ih]
private theorem refresh_cost_labels {A : Type*} [DecidableEq A]
    (T : BDL26NativeStateRows.Samples A) (U : List A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.refreshQ T U R).operations=
      refreshLabelCost U (R.map Prod.fst) := by
  change (BDL26NativeStateRows.mapQ (BDL26NativeStateRows.refreshRowQ T U) R).operations = _
  induction R with
  | nil => rfl
  | cons row R ih =>
      cases h : (BDL26NativeStateRows.memberQ row.1 U).value <;>
        simp only [BDL26NativeStateRows.mapQ,BDL26NativeStateRows.refreshRowQ,
          h,Bool.false_eq_true,if_false,if_true,List.map_cons,refreshLabelCost,ih]
private theorem prefix_labels (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows.map Prod.fst=SR.indices (SR.count S n) := by
  induction m with
  | zero => exact BDL26NativeStateRows.initialize_order S n T
  | succ m ih =>
      exact (BDL26NativeStateRows.refresh_labels T _ _).trans ih
private theorem measurable_native_point (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (a : SR.Index S n) :
    Measurable (fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
      (prefixQ S n J hr lambda K T m).value.rows a) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hbad := measurableSet_keyBad (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J r lambda K
  have hcounters := measurable_counters (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) hbad m
  have hm : Measurable (fun T : NativeTable S n =>
      assignment (X := fun _ : Vertex (Presentation S n) => Space)
        (decodedTable S n T)
        (counters (X := fun _ : Vertex (Presentation S n) => Space)
          (U S n J r) (B S n J r lambda K) (decodedTable S n T) m) (SR.decode S n a)) :=
    (measurable_pi_apply (SR.decode S n a)).comp ((measurable_assignment hcounters).comp hd)
  have hp : Measurable (fun T : NativeTable S n =>
      (pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a).1) := by
    have he : (fun T : NativeTable S n =>
        (pointQ S n lambda (incomingQ S n J).value
          (prefixQ S n J hr lambda K T m).value.rows a).1) =
        (fun T : NativeTable S n => lambda • ((1/2 : ℝ) • J (SR.decode S n a))+
          assignment (X := fun _ : Vertex (Presentation S n) => Space)
            (decodedTable S n T)
            (counters (X := fun _ : Vertex (Presentation S n) => Space)
              (U S n J r) (B S n J r lambda K) (decodedTable S n T) m) (SR.decode S n a)) := by
      funext T
      rw [point_actual]
      have he := prefix_assignment S n J hr lambda K (decodedTable S n T) m
      rw [encoded_decoded] at he
      rw [he]
    rw [he]
    exact measurable_const.add hm
  have hc : ∀ T : NativeTable S n,
      (pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a).2=
      (SR.readQ a (incomingQ S n J).value).operations+
        readLabelCost a (SR.indices (SR.count S n))+24+2 := by
    intro T
    simp only [pointQ,pointSnapshotQuery_cost,read_cost_labels,prefix_labels]
  have he : (fun T : NativeTable S n =>
      pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows a) =
      (fun T : NativeTable S n =>
        ((pointQ S n lambda (incomingQ S n J).value
          (prefixQ S n J hr lambda K T m).value.rows a).1,
          (SR.readQ a (incomingQ S n J).value).operations+
            readLabelCost a (SR.indices (SR.count S n))+24+2)) := by
    funext T
    exact Prod.ext (by rfl) (hc T)
  rw [he]
  exact hp.prodMk measurable_const
private theorem measurable_native_triangle (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (c : MD.Code) (center : Space) :
    Measurable (fun T : NativeTable S n => triangleCodeQ S n J lambda
      (prefixQ S n J hr lambda K T m).value.rows c center) := by
  cases hf : (MD.atlasReadQ c (MD.atlasQ S n).value).value with
  | none => simp only [triangleCodeQ,hf]; exact measurable_const
  | some v =>
      let x := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.1
      let y := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.2.1
      let z := fun T : NativeTable S n => pointQ S n lambda (incomingQ S n J).value
        (prefixQ S n J hr lambda K T m).value.rows v.2.2
      have hx : Measurable x := measurable_native_point S n J hr lambda K m v.1
      have hy : Measurable y := measurable_native_point S n J hr lambda K m v.2.1
      have hz : Measurable z := measurable_native_point S n J hr lambda K m v.2.2
      have hq : Measurable (fun T : NativeTable S n =>
          triangleQuery ![(x T).1,(y T).1,(z T).1] center 2) := by
        refine measurable_triangleQuery
          (fun T : NativeTable S n => ![(x T).1,(y T).1,(z T).1])
          (fun _ => center) (fun _ => (2 : ℝ)) ?_ ?_ measurable_const
        · intro i j
          fin_cases i
          · change Measurable (fun T : NativeTable S n => (x T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hx.fst
          · change Measurable (fun T : NativeTable S n => (y T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hy.fst
          · change Measurable (fun T : NativeTable S n => (z T).1 j)
            exact (PiLp.continuous_apply (2 : ℝ≥0∞)
              (fun _ : Fin 3 => ℝ) j).measurable.comp hz.fst
        · intro j
          exact measurable_const
      have hc : Measurable (fun T : NativeTable S n =>
          (MD.atlasQ S n).operations+(MD.atlasReadQ c (MD.atlasQ S n).value).operations+
          (incomingQ S n J).operations+(x T).2+(y T).2+(z T).2+
          (triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).2+4) :=
        (((((measurable_const.add hx.snd).add hy.snd).add hz.snd).add hq.snd).add measurable_const)
      have he : (fun T : NativeTable S n => triangleCodeQ S n J lambda
          (prefixQ S n J hr lambda K T m).value.rows c center) =
          (fun T : NativeTable S n =>
            ((triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).1,
              (MD.atlasQ S n).operations+(MD.atlasReadQ c (MD.atlasQ S n).value).operations+
                (incomingQ S n J).operations+(x T).2+(y T).2+(z T).2+
                (triangleQuery ![(x T).1,(y T).1,(z T).1] center 2).2+4)) := by
        funext T
        simp only [triangleCodeQ,hf,x,y,z]
      rw [he]
      exact hq.fst.prodMk hc
private theorem measurable_native_event_query (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) (row : LiveRow S n J r) :
    Measurable (fun T : NativeTable S n => eventQueryQ S n J r lambda K row
      (prefixQ S n J hr lambda K T m).value.rows) := by
  have hq := measurable_listAnyQuery (fun g : Grid K => fun T : NativeTable S n =>
    let center := centerQ S n J lambda K row.val.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n J lambda
      (prefixQ S n J hr lambda K T m).value.rows c center.1) (MC.codeList row.val.val.1)
    (triangles.1,center.2+triangles.2+2)) (by
      intro g
      have ht := measurable_listAllQuery
        (fun c => fun T : NativeTable S n => triangleCodeQ S n J lambda
          (prefixQ S n J hr lambda K T m).value.rows c
          (centerQ S n J lambda K row.val.val.1 g).1)
        (fun c => measurable_native_triangle S n J hr lambda K m c _)
        (MC.codeList row.val.val.1)
      exact ht.fst.prodMk ((measurable_const.add ht.snd).add measurable_const))
    (gridListQuery K).1
  exact hq.fst.prodMk ((measurable_const.add hq.snd).add measurable_const)
private theorem scan_pair (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    scanQ S n J hr lambda K R =
      ((scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).1,
        (universeQ S n J hr).2+
          (scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).2+1) := by
  rfl
private theorem scanQuery_precompose {A W Ω : Type*}
    (q : A → W → Bool × ℕ) (f : Ω → W) (L : List A) (w : Ω) :
    scanQuery (fun a t => q a (f t)) L w=scanQuery q L (f w) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [scanQuery,ih]
private theorem measurable_scanQuery_precompose {A W Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace (Option A)]
    (q : A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun w => q a (f w))) (L : List A) :
    Measurable (fun w => scanQuery q L (f w)) := by
  have he : (fun w => scanQuery q L (f w))=
      scanQuery (fun a t => q a (f t)) L := by
    funext w
    exact (scanQuery_precompose q f L w).symm
  rw [he]
  exact measurable_scanQuery (fun a t => q a (f t)) hq L
private theorem measurable_native_scan (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) :
    Measurable (fun T : NativeTable S n => scanQ S n J hr lambda K
      (prefixQ S n J hr lambda K T m).value.rows) := by
  have hs := measurable_scanQuery_precompose
    (eventQueryQ S n J r lambda K)
    (fun T : NativeTable S n => (prefixQ S n J hr lambda K T m).value.rows)
    (fun row => measurable_native_event_query S n J hr lambda K m row)
    (universeQ S n J hr).1
  simp_rw [scan_pair]
  exact hs.fst.prodMk ((measurable_const.add hs.snd).add measurable_const)
private theorem measurable_native_prefix_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K m : ℕ) :
    Measurable (fun T : NativeTable S n => (prefixQ S n J hr lambda K T m).operations) := by
  induction m with
  | zero =>
      have he : (fun T : NativeTable S n => (prefixQ S n J hr lambda K T 0).operations)=
          (fun _ => incomingBudget S n+1) := by
        funext T
        exact congrArg (fun k => k+1) (BDL26NativeStateRows.initialize_cost S n T).1
      rw [he]
      exact measurable_const
  | succ m ih =>
      have hs := measurable_native_scan S n J hr lambda K m
      have hf : Measurable (fun T : NativeTable S n =>
          (SR.refreshQ T (chosenSupport S n J r
            (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
            (prefixQ S n J hr lambda K T m).value.rows).operations) := by
        simp only [refresh_cost_labels,prefix_labels]
        exact (measurable_of_countable (fun e : Option (LiveRow S n J r) =>
          refreshLabelCost (chosenSupport S n J r e) (SR.indices (SR.count S n)))).comp hs.fst
      have ha : ∀ T : NativeTable S n,
          (BDL26NativeMasterCandidates.appendQ
            (prefixQ S n J hr lambda K T m).value.trace
            [(scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1]).operations=2*m+1 := by
        intro T
        rw [(BDL26NativeMasterCandidates.append_spec _ _).2.1,
          (prefix_lengths S n J hr lambda K T m).2]
      simp_rw [prefix_operations_succ,ha]
      have hm : Measurable (fun T : NativeTable S n =>
          (prefixQ S n J hr lambda K T m).operations+
            (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).2+
            (SR.refreshQ T (chosenSupport S n J r
              (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T m).value.rows).1)
              (prefixQ S n J hr lambda K T m).value.rows).operations+
            (2*m+1)+4) := by
        have hc : Measurable (fun _ : NativeTable S n => 2*m+1) := measurable_const
        have hd : Measurable (fun _ : NativeTable S n => (4 : ℕ)) := measurable_const
        convert ((((ih.add hs.snd).add hf).add hc).add hd) using 1 <;> rfl
      exact hm
private theorem measurable_native_clock (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) : Measurable (nativeHaltTime S n J hr lambda K) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hm := (measurable_haltTime (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) (measurableSet_keyBad _ _ _ _ _ _ _)).comp hd
  convert hm using 1
  funext T
  have h := haltTime_original S n J hr lambda K (decodedTable S n T)
  change nativeHaltTime S n J hr lambda K T=
    haltTime (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J r) (B S n J r lambda K) (decodedTable S n T)
  simpa only [encoded_decoded] using h
private theorem measurableSet_native_halts (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) :
    MeasurableSet {T : NativeTable S n | NativeHalts S n J hr lambda K T} := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  convert (measurableSet_halts (X := fun _ : Vertex (Presentation S n) => Space)
    (U S n J r) (B S n J r lambda K) (measurableSet_keyBad _ _ _ _ _ _ _)).preimage hd using 1
  ext T
  have h := halts_original S n J hr lambda K (decodedTable S n T)
  change NativeHalts S n J hr lambda K T ↔
    Halts (X := fun _ : Vertex (Presentation S n) => Space)
      (U S n J r) (B S n J r lambda K) (decodedTable S n T)
  simpa only [encoded_decoded] using h
end QEC.Coding.BDL26NativeGeometricExecutionCost
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26NativeGeometricExecutionCost
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) : Measurable (nativeOperationCost S n J hr lambda K) := by
  classical
  have hp : Measurable (fun z : NativeTable S n × ℕ =>
      (prefixQ S n J hr lambda K z.1 z.2).operations) :=
    measurable_from_prod_countable_left (fun m => measurable_native_prefix_cost S n J hr lambda K m)
  have hs : Measurable (fun z : NativeTable S n × ℕ =>
      (scanQ S n J hr lambda K (prefixQ S n J hr lambda K z.1 z.2).value.rows).2) :=
    measurable_from_prod_countable_left (fun m => (measurable_native_scan S n J hr lambda K m).snd)
  have ht := measurable_id.prodMk (measurable_native_clock S n J hr lambda K)
  have hc : Measurable (fun T : NativeTable S n =>
      (((prefixQ S n J hr lambda K T (nativeHaltTime S n J hr lambda K T)).operations+
        (scanQ S n J hr lambda K (prefixQ S n J hr lambda K T
          (nativeHaltTime S n J hr lambda K T)).value.rows).2+5*SR.count S n+3 : ℕ) : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      ((((hp.comp ht).add (hs.comp ht)).add measurable_const).add measurable_const)
  convert Measurable.ite (measurableSet_native_halts S n J hr lambda K) hc
    (measurable_const : Measurable (fun _ : NativeTable S n => (∞ : ℝ≥0∞))) using 1
  funext T
  by_cases h : NativeHalts S n J hr lambda K T
  · simp only [nativeOperationCost,if_pos h,
      (native_stopping_refinement S n J hr lambda K T h).2]
  · simp only [nativeOperationCost,if_neg h]
  exact fun T => Classical.propDecidable (NativeHalts S n J hr lambda K T)
end QEC.Coding.BDL26NativeGeometricExecutionCost
