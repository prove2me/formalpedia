-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Paid.stopping_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:35:32.910521+00:00
-- url     : https://prove2.me/submissions/5f63204d-7ebe-47b3-973a-fa1d9bdbbe59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_rowMap_canonical
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_canonicalRows_labels
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_canonicalRows_length
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_scan_refinement
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_prefix_refinement
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
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_code_scan_refinement
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


attribute [local simp] QEC.Coding.BDL26NativeFiniteComposition.rowMap_canonical
attribute [local simp] QEC.Coding.BDL26NativeFiniteComposition.canonicalRows_labels
attribute [local simp] QEC.Coding.BDL26NativeFiniteComposition.canonicalRows_length
section
noncomputable section
namespace QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
private theorem initial_fee_reassociate (initial rest final : ℕ)
    (h : initial+1+rest=final) : initial+rest+1=final := by
  omega
namespace Paid
private theorem choice_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    choice S n I r lambda K T m = eraseChoice S n (rowMap S n I) r
      (BDL26NativeGeometricExecution.choice S n (rowMap S n I) hr lambda K T m) := by
  unfold choice BDL26NativeGeometricExecution.choice
  rw [(prefix_refinement S n I hr lambda K T m).1,
    (scan_refinement S n I r lambda K _).1,
    BDL26NativeGeometricJointExecution.code_scan_refinement]
private theorem first_none_loop {A C B : Type*}
    (statesAt : ℕ → A) (fee : ℕ → ℕ) (query : A → Option C × ℕ)
    (advance : A → C → A) (advanceFee : A → C → ℕ)
    (emit : A → B) (emitFee : A → ℕ)
    (stop : ℕ → A → PrefixRun (A × Option B))
    (hprefix : ∀ m row, (query (statesAt m)).1 = some row →
      statesAt (m+1) = advance (statesAt m) row)
    (hfee : ∀ m row, (query (statesAt m)).1 = some row →
      fee (m+1) = fee m+(query (statesAt m)).2+advanceFee (statesAt m) row+4)
    (hnone : ∀ fuel state, (query state).1 = none →
      stop (fuel+1) state = ⟨(state,some (emit state)),(query state).2+emitFee state+3⟩)
    (hsome : ∀ fuel state row, (query state).1 = some row →
      stop (fuel+1) state =
        ⟨(stop fuel (advance state row)).value,
          (query state).2+advanceFee state row+(stop fuel (advance state row)).operations+4⟩)
    (d : ℕ) : ∀ m,
      (∀ i<d, (query (statesAt (m+i))).1 ≠ none) →
      (query (statesAt (m+d))).1 = none →
      (stop (d+1) (statesAt m)).value = (statesAt (m+d),some (emit (statesAt (m+d)))) ∧
      fee m+(stop (d+1) (statesAt m)).operations =
        fee (m+d)+(query (statesAt (m+d))).2+emitFee (statesAt (m+d))+3 := by
  induction d with
  | zero =>
      intro m hb hs
      simp only [Nat.add_zero] at hs ⊢
      rw [hnone 0 (statesAt m) hs]
      constructor
      · rfl
      · change fee m+((query (statesAt m)).2+emitFee (statesAt m)+3) =
          fee m+(query (statesAt m)).2+emitFee (statesAt m)+3
        simp only [Nat.add_assoc]
  | succ d ih =>
      intro m hb hs
      have hne := hb 0 (by omega)
      simp only [Nat.add_zero] at hne
      cases hq : (query (statesAt m)).1 with
      | none => exact False.elim (hne hq)
      | some row =>
          have hb' : ∀ i<d, (query (statesAt (m+1+i))).1 ≠ none := by
            intro i hi
            simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hb (i+1) (by omega)
          have hs' : (query (statesAt (m+1+d))).1 = none := by
            simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs
          have hrec := ih (m+1) hb' hs'
          have hm : m+1+d=m+(d+1) := by omega
          rw [hm] at hrec
          rw [hsome (d+1) (statesAt m) row hq,←hprefix m row hq]
          have hf := hfee m row hq
          refine ⟨hrec.1,?_⟩
          dsimp only
          omega
private theorem prefixRun_fee_group {A : Type*} (rest : PrefixRun A)
    (query refresh append : ℕ) :
    (⟨rest.value,query+refresh+append+rest.operations+4⟩ : PrefixRun A) =
      ⟨rest.value,query+(refresh+append)+rest.operations+4⟩ := by
  have h : query+refresh+append+rest.operations+4 =
      query+(refresh+append)+rest.operations+4 := by omega
  exact congrArg (fun fee : ℕ => (⟨rest.value,fee⟩ : PrefixRun A)) h
private theorem stop_at_first_none (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (d : ℕ) :
    ∀ m : ℕ,
      (∀ i<d,choice S n I r lambda K T (m+i)≠none) →
      choice S n I r lambda K T (m+d)=none →
      (stopFromQ S n I r lambda K T (d+1) (prefixQ S n I r lambda K T m).value).value =
        ((prefixQ S n I r lambda K T (m+d)).value,
          some (BDL26NativeStateRows.emitQ
            (prefixQ S n I r lambda K T (m+d)).value.1).value) ∧
      (prefixQ S n I r lambda K T m).operations+
        (stopFromQ S n I r lambda K T (d+1) (prefixQ S n I r lambda K T m).value).operations =
        (prefixQ S n I r lambda K T (m+d)).operations+
          (codeScanQ S n I r lambda K (prefixQ S n I r lambda K T (m+d)).value.1).2+
          (BDL26NativeStateRows.emitQ
            (prefixQ S n I r lambda K T (m+d)).value.1).operations+3 := by
  let query : State S n → Option (Code S n) × ℕ :=
    fun state => codeScanQ S n I r lambda K state.1
  let advance : State S n → Code S n → State S n := fun state row =>
    ((SR.refreshQ T (codeSupport S n (some row)) state.1).value,
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).value)
  let advanceFee : State S n → Code S n → ℕ := fun state row =>
    (SR.refreshQ T (codeSupport S n (some row)) state.1).operations+
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).operations
  have hp : ∀ m row, (query (prefixQ S n I r lambda K T m).value).1=some row →
      (prefixQ S n I r lambda K T (m+1)).value=
        advance (prefixQ S n I r lambda K T m).value row := by
    intro m row hq
    dsimp only [query] at hq
    simp only [prefixQ,query,advance,hq]
  have hc : ∀ m row, (query (prefixQ S n I r lambda K T m).value).1=some row →
      (prefixQ S n I r lambda K T (m+1)).operations=
        (prefixQ S n I r lambda K T m).operations+
          (query (prefixQ S n I r lambda K T m).value).2+
          advanceFee (prefixQ S n I r lambda K T m).value row+4 := by
    intro m row hq
    dsimp only [query] at hq
    simp only [prefixQ,hq,query,advanceFee]
    omega
  have hn : ∀ fuel state, (query state).1=none →
      stopFromQ S n I r lambda K T (fuel+1) state =
        ⟨(state,some (BDL26NativeStateRows.emitQ state.1).value),
          (query state).2+(BDL26NativeStateRows.emitQ state.1).operations+3⟩ := by
    intro fuel state hq
    dsimp only [query] at hq
    simp only [stopFromQ,hq,query]
  have hs : ∀ fuel state row, (query state).1=some row →
      stopFromQ S n I r lambda K T (fuel+1) state =
        ⟨(stopFromQ S n I r lambda K T fuel (advance state row)).value,
          (query state).2+advanceFee state row+
            (stopFromQ S n I r lambda K T fuel (advance state row)).operations+4⟩ := by
    intro fuel state row hq
    dsimp only [query] at hq
    simp only [stopFromQ,hq]
    exact prefixRun_fee_group
      (stopFromQ S n I r lambda K T fuel (advance state row))
      (query state).2
      (SR.refreshQ T (codeSupport S n (some row)) state.1).operations
      (BDL26NativeMasterCandidates.appendQ state.2 [some row]).operations
  exact first_none_loop
    (A := State S n) (C := Code S n) (B := List (SR.Index S n × Space))
    (fun m => (prefixQ S n I r lambda K T m).value)
    (fun m => (prefixQ S n I r lambda K T m).operations)
    query advance advanceFee
    (fun state => (BDL26NativeStateRows.emitQ state.1).value)
    (fun state => (BDL26NativeStateRows.emitQ state.1).operations)
    (stopFromQ S n I r lambda K T) hp hc hn hs d
private theorem stop_initial_value (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n I r lambda K T fuel).value =
      (stopFromQ S n I r lambda K T fuel
        (prefixQ S n I r lambda K T 0).value).value := by
  rfl
private theorem stop_initial_operations (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (fuel : ℕ) :
    (stopQ S n I r lambda K T fuel).operations =
      (prefixQ S n I r lambda K T 0).operations+
        (stopFromQ S n I r lambda K T fuel
          (prefixQ S n I r lambda K T 0).value).operations := by
  change (SR.initializeQ S n T).operations+
      (stopFromQ S n I r lambda K T fuel
        ((SR.initializeQ S n T).value,[])).operations+1 =
    ((SR.initializeQ S n T).operations+1)+
      (stopFromQ S n I r lambda K T fuel
        ((SR.initializeQ S n T).value,[])).operations
  exact initial_fee_reassociate _ _ _ rfl
end Paid
namespace Decoded
end Decoded
namespace Paid
end Paid
end QEC.Coding.BDL26NativeFiniteComposition
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
open QEC.Coding.BDL26NativeFiniteComposition.Paid
namespace QEC.Coding.BDL26NativeFiniteComposition.Paid
theorem _root_.solution (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (h : NativeHalts S n (rowMap S n I) hr lambda K T) :
    (stopQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).value =
      ((prefixQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value,
        some (emitted S n I hr lambda K T)) ∧
    (stopQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).operations =
      stoppedOperations S n I hr lambda K T := by
  have ht : nativeHaltTime S n (rowMap S n I) hr lambda K T=Nat.find h := by
    simp only [nativeHaltTime,dif_pos h]
  have hb : ∀ i<Nat.find h,choice S n I r lambda K T (0+i)≠none := by
    intro i hi hn
    rw [Nat.zero_add,choice_refinement S n I hr,eraseChoice,Option.map_eq_none_iff] at hn
    exact Nat.find_min h hi hn
  have hs : choice S n I r lambda K T (0+Nat.find h)=none := by
    rw [Nat.zero_add,choice_refinement S n I hr,eraseChoice,Option.map_eq_none_iff]
    exact Nat.find_spec h
  have hf := stop_at_first_none S n I r lambda K T (Nat.find h) 0 hb hs
  simp only [Nat.zero_add] at hf
  rw [←ht] at hf
  constructor
  · rw [stop_initial_value]
    simpa only [emitted] using hf.1
  · rw [stop_initial_operations]
    simpa only [stoppedOperations] using hf.2
end QEC.Coding.BDL26NativeFiniteComposition.Paid
