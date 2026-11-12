-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.measurable_native_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:12:00.023196+00:00
-- url     : https://prove2.me/submissions/0cd1962c-686d-498a-8d56-2f9fa5f7452c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_code_scan_refinement
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_prefix_refinement
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
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_point_actual
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_complete
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_cost
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_order
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_rowsFor
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
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_filterMapQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAllQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAnyQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_pointSnapshotQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_realTest_run
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
namespace QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
private theorem read_fee {A : Type*} [DecidableEq A] (a : A)
    (R : BDL26NativeStateRows.Rows A) :
    (BDL26NativeStateRows.readQ a R).operations = readFee a (R.map Prod.fst) := by
  induction R with
  | nil => rfl
  | cons row R ih =>
      by_cases h : row.1=a <;>
        simp only [BDL26NativeStateRows.readQ,List.map_cons,readFee,h,if_true,if_false,ih]
private theorem sample_labels (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) :
    (sampleRows S n T c).map Prod.fst = SR.indices (SR.count S n) := by
  simp only [sampleRows,BDL26NativeStateRows.rowsFor,List.map_map,Function.comp_def]
  have hid (L : List (SR.Index S n)) : L.map (fun a => a) = L := by
    induction L with
    | nil => rfl
    | cons a L ih => exact congrArg (List.cons a) ih
  exact hid _
private theorem incoming_fee (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n J).operations = incomingBudget S n :=
  (BDL26NativeStateRows.initialize_cost S n _).1
private theorem incoming_labels (S : OddScale) (n : ℕ) (J : Input S n) :
    (incomingQ S n J).value.map Prod.fst = SR.indices (SR.count S n) :=
  BDL26NativeStateRows.initialize_order S n _
private theorem sample_point (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    originalPoints S n (sampleRows S n T c) (SR.decode S n a) = T (a,c a) := by
  simp only [originalPoints,BDL26NativeStateRows.points,Equiv.symm_apply_apply,sampleRows]
  rw [SR.read_rowsFor _ _ _ _ (SR.indices_complete _ _)]
private theorem measurable_point (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (a : SR.Index S n) :
    Measurable (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) a) := by
  have he : (fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) a) =
      (fun z : JointInput S n =>
        (lambda • ((1/2 : ℝ) • z.1 (SR.decode S n a))+z.2 (a,c a),
          readFee a (SR.indices (SR.count S n))+
            readFee a (SR.indices (SR.count S n))+24+2)) := by
    funext z
    apply Prod.ext
    · rw [point_actual,sample_point]
    · simp only [pointQ,pointSnapshotQuery_cost,read_fee,incoming_labels,sample_labels]
  rw [he]
  have hJ : Measurable (fun z : JointInput S n => z.1 (SR.decode S n a)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hT : Measurable (fun z : JointInput S n => z.2 (a,c a)) :=
    (measurable_pi_apply _).comp measurable_snd
  exact (((hJ.const_smul (1/2 : ℝ)).const_smul lambda).add hT).prodMk measurable_const
private theorem measurable_pair (S : OddScale) (n : ℕ) (r : ℝ)
    (a b : MD.Code) : Measurable (fun J : Input S n => pairQ S n J r a b) := by
  cases ha : (NC.colorOfCodeQ S n a).value with
  | none => simp only [pairQ,ha]; exact measurable_const
  | some A =>
    cases hb : (NC.colorOfCodeQ S n b).value with
    | none => simp only [pairQ,ha,hb]; exact measurable_const
    | some B =>
      have hq : Measurable (fun J : Input S n =>
          anchorCloseProgram.run (fun _ => J (SR.decode S n B.1.1))
            (J (SR.decode S n A.1.1)) r) := by
        apply measurable_realTest_run
        · intro i j
          exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
            (measurable_pi_apply _)
        · intro j
          exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
            (measurable_pi_apply _)
        · exact measurable_const
      have hm : Measurable (fun q : Bool × ℕ =>
          (decide (A.2=B.2) && q.1,
            (NC.colorOfCodeQ S n a).operations+(NC.colorOfCodeQ S n b).operations+
              incomingBudget S n+readFee A.1.1 (SR.indices (SR.count S n))+
              readFee B.1.1 (SR.indices (SR.count S n))+q.2+5)) :=
        measurable_of_countable _
      simpa only [pairQ,ha,hb,incoming_read,incoming_fee,read_fee,incoming_labels,
        Function.comp_def] using hm.comp hq
private theorem measurable_eligible (S : OddScale) (n : ℕ) (r : ℝ)
    (codes : MD.FourCodes) : Measurable (fun J : Input S n => eligibleQ S n J r codes) :=
  measurable_listAllQuery _
    (fun a => measurable_listAllQuery _ (measurable_pair S n r a) (MC.codeList codes))
    (MC.codeList codes)
private theorem codeUniverse_factor (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    codeUniverseQ S n J r =
      (let q := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
       let sorted := sortQuery (codeCompareQ S n) q.1
       (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
  rfl
private theorem measurable_universe (S : OddScale) (n : ℕ) (r : ℝ) :
    Measurable (fun J : Input S n => codeUniverseQ S n J r) := by
  have hc (row : Code S n) : Measurable (fun J : Input S n => codeCandidateQ S n J r row) :=
    (measurable_of_countable (fun q : Bool × ℕ =>
      (if q.1 then some row else none,q.2+1))).comp (measurable_eligible S n r row.val.1)
  have hr := measurable_filterMapQuery (fun row J => codeCandidateQ S n J r row)
    hc (MC.Rows S n).attach
  have hm : Measurable (fun q : List (Code S n) × ℕ =>
      let sorted := sortQuery (codeCompareQ S n) q.1
      (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) :=
    measurable_of_countable _
  have he : (fun J : Input S n => codeUniverseQ S n J r) =
      (fun J : Input S n =>
        let q := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
        let sorted := sortQuery (codeCompareQ S n) q.1
        (sorted.1,(MC.masterCandidatesQ S n).operations+q.2+1+sorted.2)) := by
    funext J
    exact codeUniverse_factor S n J r
  rw [he]
  exact hm.comp hr
private theorem measurable_center (S : OddScale) (n : ℕ) (lambda : ℝ)
    (K : ℕ) (codes : MD.FourCodes) (g : Grid K) :
    Measurable (fun J : Input S n => centerQ S n J lambda K codes g) := by
  cases hf : (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).value with
  | none => simp only [centerQ,hf]; exact measurable_const
  | some v =>
    have hp := measurable_pointSnapshotQuery lambda
      (fun J : Input S n => J (SR.decode S n v.1))
      (fun _ : Input S n => (gridPointQuery K g).1)
      (measurable_pi_apply _) measurable_const
    have he : (fun J : Input S n => centerQ S n J lambda K codes g) =
        (fun J : Input S n =>
          ((pointSnapshotQuery lambda (J (SR.decode S n v.1)) (gridPointQuery K g).1).1,
            (anchorCodeQ codes).2+(MD.atlasQ S n).operations+
              (MD.atlasReadQ (anchorCodeQ codes).1 (MD.atlasQ S n).value).operations+
              incomingBudget S n+readFee v.1 (SR.indices (SR.count S n))+
              (gridPointQuery K g).2+24+3)) := by
      funext J
      simp only [centerQ,hf,incoming_read,incoming_fee,read_fee,incoming_labels,
        pointSnapshotQuery_cost]
    rw [he]
    exact hp.fst.prodMk measurable_const
private theorem measurable_triangle (S : OddScale) (n : ℕ) (lambda : ℝ)
    (c : SR.Index S n → ℕ) (code : MD.Code)
    (center : JointInput S n → Space) (hc : Measurable center) :
    Measurable (fun z : JointInput S n =>
      triangleCodeQ S n z.1 lambda (sampleRows S n z.2 c) code (center z)) := by
  cases hf : (MD.atlasReadQ code (MD.atlasQ S n).value).value with
  | none => simp only [triangleCodeQ,hf]; exact measurable_const
  | some v =>
    let x := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.1
    let y := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.2.1
    let z' := fun z : JointInput S n =>
      pointQ S n lambda (incomingQ S n z.1).value (sampleRows S n z.2 c) v.2.2
    have hx : Measurable x := measurable_point S n lambda c v.1
    have hy : Measurable y := measurable_point S n lambda c v.2.1
    have hz : Measurable z' := measurable_point S n lambda c v.2.2
    have hq : Measurable (fun z : JointInput S n =>
        triangleQuery ![(x z).1,(y z).1,(z' z).1] (center z) 2) := by
      apply measurable_triangleQuery
      · intro i j
        fin_cases i
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hx.fst
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hy.fst
        · exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hz.fst
      · intro j
        exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hc
      · exact measurable_const
    have hcost : Measurable (fun z : JointInput S n =>
        (MD.atlasQ S n).operations+(MD.atlasReadQ code (MD.atlasQ S n).value).operations+
          incomingBudget S n+(x z).2+(y z).2+(z' z).2+
          (triangleQuery ![(x z).1,(y z).1,(z' z).1] (center z) 2).2+4) :=
      (((((measurable_const.add hx.snd).add hy.snd).add hz.snd).add hq.snd).add measurable_const)
    convert hq.fst.prodMk hcost using 1
    funext z
    simp only [triangleCodeQ,hf,incoming_fee,x,y,z']
private theorem measurable_paid_event_fold {Ω G A : Type*} [MeasurableSpace Ω]
    (grid : List G) (gridCost : ℕ) (codes : List A)
    (center : G → Ω → Space × ℕ) (triangle : A → Ω → Space → Bool × ℕ)
    (hc : ∀ g, Measurable (center g))
    (ht : ∀ g a, Measurable (fun z => triangle a z (center g z).1)) :
    Measurable (fun z : Ω =>
      let query := listAnyQuery (fun g =>
        let c := center g z
        let tests := listAllQuery (fun a => triangle a z c.1) codes
        (tests.1,c.2+tests.2+2)) grid
      (query.1,gridCost+query.2+1)) := by
  have hg (g : G) : Measurable (fun z : Ω =>
      let c := center g z
      let tests := listAllQuery (fun a => triangle a z c.1) codes
      (tests.1,c.2+tests.2+2)) := by
    have hall : Measurable (fun z : Ω =>
        listAllQuery (fun a => triangle a z (center g z).1) codes) :=
      measurable_listAllQuery (fun a z => triangle a z (center g z).1) (ht g) codes
    have hp : Measurable (fun v : (Bool × ℕ) × ℕ =>
        (v.1.1,v.2+v.1.2+2)) := measurable_of_countable _
    exact hp.comp (hall.prodMk (hc g).snd)
  have hq := measurable_listAnyQuery _ hg grid
  have hp : Measurable (fun v : Bool × ℕ => (v.1,gridCost+v.2+1)) :=
    measurable_of_countable _
  exact hp.comp hq
private theorem measurable_codeEvent (S : OddScale) (n : ℕ) (lambda : ℝ)
    (K : ℕ) (c : SR.Index S n → ℕ) (row : Code S n) :
    Measurable (fun z : JointInput S n =>
      codeEventQ S n z.1 lambda K row (sampleRows S n z.2 c)) := by
  let center : Grid K → JointInput S n → Space × ℕ :=
    fun g z => centerQ S n z.1 lambda K row.val.1 g
  let triangle : MD.Code → JointInput S n → Space → Bool × ℕ :=
    fun a z w => triangleCodeQ S n z.1 lambda (sampleRows S n z.2 c) a w
  have hc (g : Grid K) : Measurable (center g) :=
    (measurable_center S n lambda K row.val.1 g).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have ht (g : Grid K) (a : MD.Code) :
      Measurable (fun z : JointInput S n => triangle a z (center g z).1) :=
    measurable_triangle S n lambda c a _ (hc g).fst
  have hm := measurable_paid_event_fold (gridListQuery K).1 (gridListQuery K).2
    (MC.codeList row.val.1) center triangle hc ht
  have he : (fun z : JointInput S n =>
      codeEventQ S n z.1 lambda K row (sampleRows S n z.2 c)) =
      (fun z : JointInput S n =>
        let query := listAnyQuery (fun g =>
          let w := center g z
          let tests := listAllQuery (fun a => triangle a z w.1) (MC.codeList row.val.1)
          (tests.1,w.2+tests.2+2)) (gridListQuery K).1
        (query.1,(gridListQuery K).2+query.2+1)) := by
    funext z
    rfl
  rw [he]
  exact hm
private theorem scan_curry {A W Ω : Type*}
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W) (L : List A) (z : Ω) :
    scanQuery (fun a w => q w a (f w)) L z = scanQuery (q z) L (f z) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [scanQuery,ih]
private theorem measurable_scan_curry {A W Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace (Option A)]
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun z => q z a (f z))) (L : List A) :
    Measurable (fun z => scanQuery (q z) L (f z)) := by
  have he : (fun z => scanQuery (q z) L (f z)) =
      scanQuery (fun a z => q z a (f z)) L := by
    funext z
    exact (scan_curry q f L z).symm
  rw [he]
  exact measurable_scanQuery (fun a z => q z a (f z)) hq L
private theorem measurable_paid_scan {Ω A W : Type*} [MeasurableSpace Ω]
    [Countable A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (Option A)] [MeasurableSingletonClass (Option A)]
    (q : Ω → A → W → Bool × ℕ) (f : Ω → W)
    (hq : ∀ a, Measurable (fun z => q z a (f z)))
    (candidates : Ω → List A × ℕ) (hu : Measurable candidates) :
    Measurable (fun z : Ω =>
      let scan := scanQuery (q z) (candidates z).1 (f z)
      (scan.1,(candidates z).2+scan.2+1)) := by
  have hscan (L : List A) : Measurable (fun z : Ω => scanQuery (q z) L (f z)) :=
    measurable_scan_curry q f hq L
  have hm : Measurable (fun z : Ω × List A => scanQuery (q z.1) z.2 (f z.1)) :=
    measurable_from_prod_countable_left hscan
  have hs := hm.comp (measurable_id.prodMk hu.fst)
  have hp : Measurable (fun v : (Option A × ℕ) × ℕ =>
      (v.1.1,v.2+v.1.2+1)) := measurable_of_countable _
  exact hp.comp (hs.prodMk hu.snd)
private theorem measurable_codeScan (S : OddScale) (n : ℕ) (r lambda : ℝ)
    (K : ℕ) (c : SR.Index S n → ℕ) :
    Measurable (fun z : JointInput S n =>
      codeScanQ S n z.1 r lambda K (sampleRows S n z.2 c)) := by
  let q : JointInput S n → Code S n → SR.Rows (SR.Index S n) → Bool × ℕ :=
    fun z => codeEventQ S n z.1 lambda K
  let f : JointInput S n → SR.Rows (SR.Index S n) := fun z => sampleRows S n z.2 c
  let candidates : JointInput S n → List (Code S n) × ℕ :=
    fun z => codeUniverseQ S n z.1 r
  have hq (a : Code S n) : Measurable (fun z : JointInput S n => q z a (f z)) :=
    measurable_codeEvent S n lambda K c a
  have hu : Measurable candidates :=
    (measurable_universe S n r).comp
      (measurable_fst : Measurable (fun z : JointInput S n => z.1))
  have hm := measurable_paid_scan q f hq candidates hu
  have he : (fun z : JointInput S n =>
      codeScanQ S n z.1 r lambda K (sampleRows S n z.2 c)) =
      (fun z : JointInput S n =>
        let scan := scanQuery (q z) (candidates z).1 (f z)
        (scan.1,(candidates z).2+scan.2+1)) := by
    funext z
    rfl
  rw [he]
  exact hm
private theorem measurable_counted_step {A B : Type*} [Fintype A] [DecidableEq A]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (support : Option B → List A) (addresses : List A) :
    Measurable (fun w : ((A → ℕ) × List (Option B) × ℕ) × (Option B × ℕ) =>
      (SR.advanceList (support w.2.1) w.1.1,
        w.1.2.1++[w.2.1],
        w.1.2.2+w.2.2+refreshFee (support w.2.1) addresses+
          (2*w.1.2.1.length+1)+4)) :=
  measurable_of_countable _
private theorem measurable_counted_transition {Ω A B : Type*} [MeasurableSpace Ω]
    [Fintype A] [DecidableEq A]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (support : Option B → List A) (addresses : List A)
    (prior next : Ω → (A → ℕ) × List (Option B) × ℕ)
    (chosen : Ω → Option B × ℕ)
    (hp : Measurable prior) (hq : Measurable chosen)
    (he : ∀ z, next z =
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) : Measurable next := by
  have hm := measurable_counted_step support addresses
  have hc : Measurable (fun z : Ω =>
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) := hm.comp (hp.prodMk hq)
  have heq : next = (fun z : Ω =>
      (SR.advanceList (support (chosen z).1) (prior z).1,
        (prior z).2.1++[(chosen z).1],
        (prior z).2.2+(chosen z).2+refreshFee (support (chosen z).1) addresses+
          (2*(prior z).2.1.length+1)+4)) := funext he
  rw [heq]
  exact hc
private theorem countedPrefix_succ_pair (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    countedPrefix S n J r lambda K T (m+1) =
      (let prior := countedPrefix S n J r lambda K T m
       let chosen := codeScanQ S n J r lambda K (sampleRows S n T prior.1)
       (SR.advanceList (codeSupport S n chosen.1) prior.1,
         prior.2.1++[chosen.1],
         prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
           (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)) := by
  rfl
private theorem measurable_prior_fst_query {Ω R E C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace E] [MeasurableSpace C]
    (prior : Ω → R × E) (query : Ω × R → C) (chosen : Ω → C)
    (hp : Measurable prior) (hq : Measurable query)
    (he : ∀ z, chosen z = query (z,(prior z).1)) : Measurable chosen := by
  have hm : Measurable (fun z : Ω => query (z,(prior z).1)) :=
    hq.comp (measurable_id.prodMk hp.fst)
  have heq : chosen = (fun z : Ω => query (z,(prior z).1)) := funext he
  rw [heq]
  exact hm
private theorem measurable_countedPrefix (S : OddScale) (n : ℕ)
    (r lambda : ℝ) (K m : ℕ) : Measurable (fun z : JointInput S n =>
      countedPrefix S n z.1 r lambda K z.2 m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    let prior : JointInput S n → CountState S n :=
      fun z => countedPrefix S n z.1 r lambda K z.2 m
    let chosen : JointInput S n → Option (Code S n) × ℕ :=
      fun z => codeScanQ S n z.1 r lambda K (sampleRows S n z.2 (prior z).1)
    have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
        codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2)) :=
      measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
    have hp : Measurable prior := ih
    have hq : Measurable chosen :=
      measurable_prior_fst_query
        (Ω := JointInput S n) (R := SR.Index S n → ℕ)
        (E := Trace S n × ℕ) (C := Option (Code S n) × ℕ)
        prior
        (fun w : JointInput S n × (SR.Index S n → ℕ) =>
          codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2))
        chosen hp hs (fun _ => rfl)
    exact measurable_counted_transition (codeSupport S n) (SR.indices (SR.count S n))
      prior (fun z => countedPrefix S n z.1 r lambda K z.2 (m+1)) chosen hp hq
      (fun z => countedPrefix_succ_pair S n z.1 r lambda K z.2 m)
end QEC.Coding.BDL26NativeGeometricJointExecution
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
namespace QEC.Coding.BDL26NativeGeometricJointExecution
theorem _root_.solution (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K m : ℕ) : Measurable
    (fun z : JointInput S n =>
      (codedChoice S n z.1 hr lambda K z.2 m,
        (scanQ S n z.1 hr lambda K (prefixQ S n z.1 hr lambda K z.2 m).value.rows).2)) := by
  have hp := measurable_countedPrefix S n r lambda K m
  have hs : Measurable (fun w : JointInput S n × (SR.Index S n → ℕ) =>
      codeScanQ S n w.1.1 r lambda K (sampleRows S n w.1.2 w.2)) :=
    measurable_from_prod_countable_left (measurable_codeScan S n r lambda K)
  convert hs.comp (measurable_id.prodMk hp.fst) using 1
  funext z
  change (eraseChoice S n z.1 r
      (scanQ S n z.1 hr lambda K
        (prefixQ S n z.1 hr lambda K z.2 m).value.rows).1,
      (scanQ S n z.1 hr lambda K
        (prefixQ S n z.1 hr lambda K z.2 m).value.rows).2) =
    codeScanQ S n z.1 r lambda K
      (sampleRows S n z.2 (countedPrefix S n z.1 r lambda K z.2 m).1)
  rw [← (native_prefix_refinement S n z.1 hr lambda K z.2 m).1,
    code_scan_refinement]
end QEC.Coding.BDL26NativeGeometricJointExecution
