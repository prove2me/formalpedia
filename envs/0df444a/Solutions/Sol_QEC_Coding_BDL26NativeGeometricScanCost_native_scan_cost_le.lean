-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricScanCost.native_scan_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:32:54.953749+00:00
-- url     : https://prove2.me/submissions/82286183-c3b4-45ad-998d-7bd625104782

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
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
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_compare_actual
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_universe_sort_cost
import Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_count
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_length
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_cost
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_value
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_cost
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_cost
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_value
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_cost
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_cost
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
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_anchorCloseProgram_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_filterMapQuery_length_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridListQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridListQuery_length
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gridPointQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_listAllQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_listAnyQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleQuery_cost_le
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
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_run_cost_le
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
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
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
private theorem codeList_length (codes : MD.FourCodes) :
    (MC.codeList codes).length=4 := rfl
private theorem incoming_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) :
    (incomingQ S n J).value.length=SR.count S n := by
  rw [incomingQ, SR.initialize_value]
  simp only [BDL26NativeStateRows.rowsFor, List.length_map,
    BDL26NativeStateRows.indices_length]
private theorem incoming_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) :
    (incomingQ S n J).operations=incomingBudget S n := by
  exact (BDL26NativeStateRows.initialize_cost S n
    (fun p => J (SR.decode S n p.1))).1
private theorem atlas_read_cost (S : OddScale) (n : ℕ) (c : MD.Code) :
    (MD.atlasReadQ c (MD.atlasQ S n).value).operations ≤ atlasReadBudget S n := by
  have h := (BDL26NativeSupportMetadata.atlas_read_cost c (MD.atlasQ S n).value).1
  simpa only [atlasReadBudget,triangleCount,
    BDL26NativeSupportMetadata.atlas_value,List.length_map] using h
private theorem color_cost (S : OddScale) (n : ℕ) (c : MD.Code) :
    (NC.colorOfCodeQ S n c).operations ≤ colorBudget S n := by
  exact (BDL26NativeTriangleColors.lookup_cost S n c).1
private theorem pair_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (a b : MD.Code) :
    (pairQ S n J r a b).2 ≤ pairBudget S n := by
  have hA := color_cost S n a
  have hB := color_cost S n b
  have hI := incoming_cost S n J
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none =>
      simp only [pairQ, ha]
      dsimp only [pairBudget]
      omega
  | some aa =>
      rcases aa with ⟨ca,xa⟩
      cases hb : (NC.colorOfCodeQ S n b).value with
      | none =>
          simp only [pairQ, ha, hb]
          dsimp only [pairBudget]
          omega
      | some bb =>
          rcases bb with ⟨cb,xb⟩
          have hx := (BDL26NativeStateRows.read_cost ca.1 (incomingQ S n J).value).1
          have hy := (BDL26NativeStateRows.read_cost cb.1 (incomingQ S n J).value).1
          rw [incoming_length] at hx hy
          have hc := anchorCloseProgram.run_cost_le
            (fun _ => (SR.readQ cb.1 (incomingQ S n J).value).value.2)
            (SR.readQ ca.1 (incomingQ S n J).value).value.2 r
          have hp := anchorCloseProgram_cost_le
          simp only [pairQ, ha, hb]
          dsimp only [pairBudget]
          omega
private theorem eligibility_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (codes : MD.FourCodes) :
    (eligibleQ S n J r codes).2 ≤ eligibilityBudget S n := by
  have h := listAllQuery_cost_le
    (fun a => listAllQuery (pairQ S n J r a) (MC.codeList codes))
    (MC.codeList codes) (4*(pairBudget S n+1)) (by
      intro a ha
      have h := listAllQuery_cost_le (pairQ S n J r a) (MC.codeList codes)
        (pairBudget S n) (by intro b hb; exact pair_cost S n J r a b)
      simpa only [codeList_length] using h)
  simpa only [eligibleQ, eligibilityBudget, codeList_length] using h
private theorem candidate_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (row : GeneratedRow S n) :
    (candidateQ S n J hr row).2 ≤ eligibilityBudget S n+1 := by
  have h := eligibility_cost S n J r row.val.1
  unfold candidateQ
  dsimp only
  split_ifs <;> exact Nat.add_le_add_right h 1
private theorem raw_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (rawUniverseQ S n J hr).1.length ≤ masterCount S n := by
  have h := filterMapQuery_length_le (candidateQ S n J hr)
    (MC.masterCandidatesQ S n).value.attach
  rw [List.length_attach] at h
  change (rawUniverseQ S n J hr).1.length ≤ (MC.Rows S n).length at h
  exact h.trans_eq (BDL26NativeMasterCandidates.master_count S n)
private theorem raw_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (rawUniverseQ S n J hr).2 ≤ (MC.masterCandidatesQ S n).operations+
      masterCount S n*(eligibilityBudget S n+2)+1 := by
  have h := filterMapQuery_cost_le (candidateQ S n J hr)
    (MC.masterCandidatesQ S n).value.attach (eligibilityBudget S n+1)
    (by intro row hrow; exact candidate_cost S n J hr row)
  rw [List.length_attach] at h
  have hm : (MC.masterCandidatesQ S n).value.length=masterCount S n :=
    BDL26NativeMasterCandidates.master_count S n
  rw [hm] at h
  norm_num only [Nat.add_assoc] at h
  change (MC.masterCandidatesQ S n).operations+
    (filterMapQuery (candidateQ S n J hr) (MC.masterCandidatesQ S n).value.attach).2+1 ≤ _
  omega
private theorem universe_length (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).1.length ≤ masterCount S n := by
  change (sortQuery (compareQ S n J r) (rawUniverseQ S n J hr).1).1.length ≤ _
  rw [sortQuery_value (compareQ S n J r)
    (fun a b => BDL26KeyedGeometricExecution.keyPriorityLE (Presentation S n)
      (NC.nativeKey S n) (NC.nativeKey_injective S n) J r
      (event S n J r a) (event S n J r b)) (compare_actual S n J r),
    List.length_insertionSort]
  exact raw_length S n J hr
private theorem universe_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).2 ≤ preprocessingBudget S n := by
  have h := universe_sort_cost S n J hr
  have hraw := raw_cost S n J hr
  have hl := raw_length S n J hr
  have hs := Nat.mul_le_mul_right 159
    (Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) 2)
  dsimp only [preprocessingBudget]
  omega
private theorem point_cost (S : OddScale) (n : ℕ) (lambda : ℝ)
    (I R : SR.Rows (SR.Index S n)) (a : SR.Index S n) :
    (pointQ S n lambda I R a).2 ≤ pointBudget I.length R.length := by
  have hi := (BDL26NativeStateRows.read_cost a I).1
  have hr := (BDL26NativeStateRows.read_cost a R).1
  have hp := pointSnapshotQuery_cost_le lambda
    (SR.readQ a I).value.2 (SR.readQ a R).value.2
  change (SR.readQ a I).operations+(SR.readQ a R).operations+
    (pointSnapshotQuery lambda (SR.readQ a I).value.2 (SR.readQ a R).value.2).2+2 ≤ _
  dsimp only [pointBudget]
  omega
private theorem triangle_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (lambda : ℝ)
    (R : SR.Rows (SR.Index S n)) (c : MD.Code) (center : Space) :
    (triangleCodeQ S n J lambda R c center).2 ≤ triangleBudget S n R.length := by
  have ha := atlas_read_cost S n c
  have hi := incoming_cost S n J
  cases hf : (MD.atlasReadQ c (MD.atlasQ S n).value).value with
  | none =>
      simp only [triangleCodeQ, hf]
      dsimp only [triangleBudget]
      omega
  | some v =>
      have hx := point_cost S n lambda (incomingQ S n J).value R v.1
      have hy := point_cost S n lambda (incomingQ S n J).value R v.2.1
      have hz := point_cost S n lambda (incomingQ S n J).value R v.2.2
      rw [incoming_length] at hx hy hz
      have hq := triangleQuery_cost_le ![
        (pointQ S n lambda (incomingQ S n J).value R v.1).1,
        (pointQ S n lambda (incomingQ S n J).value R v.2.1).1,
        (pointQ S n lambda (incomingQ S n J).value R v.2.2).1] center 2
      simp only [triangleCodeQ, hf]
      dsimp only [triangleBudget]
      omega
private theorem lower_cost (a b : MD.Code) : (lowerCodeQ a b).2=11 := rfl
private theorem anchor_fold_cost (a : MD.Code) (L : List MD.Code) :
    (anchorFoldQ a L).2=12*L.length := by
  induction L generalizing a with
  | nil => rfl
  | cons b L ih =>
      change (lowerCodeQ a b).2+(anchorFoldQ (lowerCodeQ a b).1 L).2+1=
        12*(L.length+1)
      rw [lower_cost, ih]
      ring
private theorem anchor_cost (codes : MD.FourCodes) : (anchorCodeQ codes).2=36 :=
  anchor_fold_cost codes.first [codes.second,codes.third,codes.fourth]
private theorem center_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (lambda : ℝ) (K : ℕ)
    (codes : MD.FourCodes) (g : Grid K) :
    (centerQ S n J lambda K codes g).2 ≤ centerBudget S n K := by
  have ha := atlas_read_cost S n (anchorCodeQ codes).1
  have hi := incoming_cost S n J
  have hc := anchor_cost codes
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none =>
      simp only [centerQ, hf]
      dsimp only [centerBudget]
      omega
  | some v =>
      have hj := (BDL26NativeStateRows.read_cost v.1 (incomingQ S n J).value).1
      rw [incoming_length] at hj
      have hg := gridPointQuery_cost_le K g
      have hp := pointSnapshotQuery_cost_le lambda
        (SR.readQ v.1 (incomingQ S n J).value).value.2 (gridPointQuery K g).1
      simp only [centerQ, hf]
      dsimp only [centerBudget]
      omega
private theorem event_query_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (R : SR.Rows (SR.Index S n)) :
    (eventQueryQ S n J r lambda K row R).2 ≤ queryBudget S n K R.length := by
  have hg := gridListQuery_cost_le K
  have hq := listAnyQuery_cost_le (fun g : Grid K =>
    let center := centerQ S n J lambda K row.val.val.1 g
    let triangles := listAllQuery
      (fun c => triangleCodeQ S n J lambda R c center.1) (MC.codeList row.val.val.1)
    (triangles.1,center.2+triangles.2+2))
    (gridListQuery K).1
    (centerBudget S n K+4*(triangleBudget S n R.length+1)+2) (by
      intro g hgm
      have hc := center_cost S n J lambda K row.val.val.1 g
      have ht := listAllQuery_cost_le
        (fun c => triangleCodeQ S n J lambda R c
          (centerQ S n J lambda K row.val.val.1 g).1)
        (MC.codeList row.val.val.1) (triangleBudget S n R.length)
        (by intro c hcm; exact triangle_cost S n J lambda R c _)
      rw [codeList_length] at ht
      dsimp only
      omega)
  rw [gridListQuery_length] at hq
  change (gridListQuery K).2+
    (listAnyQuery _ (gridListQuery K).1).2+1 ≤ _
  dsimp only [queryBudget, gridBudget]
  norm_num only [Nat.add_assoc] at hq ⊢
  omega
private theorem scan_list_cost {A W : Type*} (q : A → W → Bool × ℕ)
    (L : List A) (w : W) (C : ℕ) (hq : ∀ a, (q a w).2 ≤ C) :
    (scanQuery q L w).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [scanQuery]
  | cons a L ih =>
      have ha := hq a
      simp only [scanQuery, List.length_cons]
      split_ifs <;> nlinarith
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
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (scanQ S n J hr lambda K R).2 ≤ scanBudget S n K R.length := by
  have hu := universe_cost S n J hr
  have hl := universe_length S n J hr
  have hs := scan_list_cost (eventQueryQ S n J r lambda K)
    (universeQ S n J hr).1 R (queryBudget S n K R.length)
    (fun row => event_query_cost_le S n J r lambda K row R)
  have hm := Nat.mul_le_mul_right (queryBudget S n K R.length+1) hl
  change (universeQ S n J hr).2+
    (scanQuery (eventQueryQ S n J r lambda K) (universeQ S n J hr).1 R).2+1 ≤ _
  dsimp only [scanBudget]
  omega
end QEC.Coding.BDL26NativeGeometricScanCost
