-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_mid_Q_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:12:59.511423+00:00
-- url     : https://prove2.me/submissions/802b39b8-28a0-4b94-b5c6-9e0bed5832be

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_mid_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_base_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_mid_Z_marked
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_mid_Z_parent
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_nonzero_Q_coordinate
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_mid_input_owner_marked
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_Q_coordinate_owner
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_baseMarks
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_rootComponent
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_root_path
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_base
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_root_marked_iff_parented_base
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_transpose_wordEquiv_symm
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zPairEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
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
import Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26UniformTopOwnerIsolation_markedAdjacent_iff
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
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
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_base
attribute [local simp] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_coarse
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_components
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_correction
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.qSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.regionExtension_apply
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xCorrectionEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_other
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xLift_same
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.xSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.zPairEquiv_val
attribute [local simp] QEC.Coding.BDL26RXDecoderAdapter.zSyndromeEquiv_val
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_coarse
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components
attribute [local simp] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_correction
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzFace_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
attribute [local simp] QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.map2Coord_canonicalBasis
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply
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
attribute [local simp] QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26UniformTopOwnerIsolation.markedAdjacent_iff
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.copiedQ_image_vertical
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_copy
attribute [local simp] QEC.Coding.BDL26XLocalConnectingWeight.verticalZ_image_vertical
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.RZCoarseGraining.coarseSyndrome_coe
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem zVertex_eq (S : OddScale) (n : Nat) (z : (state S n).presentation.Z) :
    zVertex S n z = @Vertex.z (state S n).presentation z := rfl
private theorem actualBaseNode_physical (S : OddScale) (v : GraphVertex S 2) :
    actualBaseNode S v = BDL26CanonicalHistoryMarks.physicalNode S 2 (0 : LevelIndex 2) v := rfl
private theorem actualMidNode_literal (S : OddScale) (v : GraphVertex S 3) :
    actualMidNode S v =
      (⟨(2 : StepIndex 4).succ,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl
private theorem actualBaseNode_literal (S : OddScale) (v : GraphVertex S 2) :
    actualBaseNode S v =
      (⟨(2 : StepIndex 4).castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S 2) := rfl
private theorem mask_filter_apply {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Prop) [DecidablePred P] (word : I → BDL26Field) (p : I) :
    maskWord (Finset.univ.filter P) word p = if P p then word p else 0 := by
  simp only [maskWord,Finset.mem_filter,Finset.mem_univ,true_and]
private theorem selected_value_eq {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : word p ≠ 0 → P p) :
    (if P p then word p else 0) = word p := by
  by_cases hz : word p = 0
  · by_cases hk : P p
    · exact if_pos hk
    · exact (if_neg hk).trans hz.symm
  · exact if_pos (hp hz)
private theorem selectedWord_apply {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) :
    selectedWord P word p = if P p then word p else 0 := rfl
private theorem selectedWord_preserves {I : Type} (P : I → Prop) [DecidablePred P]
    (word : I → BDL26Field) (p : I) (hp : word p ≠ 0 → P p) :
    selectedWord P word p = word p :=
  (selectedWord_apply P word p).trans (selected_value_eq P word p hp)
private theorem selectedWord_congr_iff {I : Type} (P Q : I → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ p, P p ↔ Q p)
    (word : I → BDL26Field) : selectedWord P word = selectedWord Q word := by
  funext p
  by_cases hp : P p
  · have hq : Q p := (h p).mp hp
    simp only [selectedWord_apply,if_pos hp,if_pos hq]
  · have hq : ¬Q p := fun hq => hp ((h p).mpr hq)
    simp only [selectedWord_apply,if_neg hp,if_neg hq]
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction
private theorem base_r2_owner (S : OddScale) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S 2 (r2 S) =
      zVertex S 1 (baseRetainedZ S) := by
  change @Vertex.z (state S 1).presentation (baseRetainedZ S) =
    zVertex S 1 (baseRetainedZ S)
  exact (zVertex_eq S 1 (baseRetainedZ S)).symm
private theorem base_retained_parent (S : OddScale) :
    parent S 1 (zVertex S 1 (baseRetainedZ S)) = some (zVertex S 0 (seedZ S)) := by
  change rxParent baseTannerSquarePresentation S
    (Vertex.z (Sum.inr (seedZ S,0))) = some (Vertex.z (seedZ S))
  rfl
private theorem actual_base_retained_marked (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    zVertex S 1 (baseRetainedZ S) ∈ BDL26CanonicalHistoryMarks.baseMarks S 2 sigma := by
  have hvalue : (gamma2 S).val (r2 S) ≠ 0 :=
    fun hz => one_ne_zero ((gamma2_at_r2 S).symm.trans hz)
  have heval : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) =
      (gamma2 S).val (r2 S) :=
    congrArg (fun word :
      (BDL26CanonicalHistoryMarks.Data S 2).family.Syndrome (0 : LevelIndex 2) =>
        word.val (r2 S)) hbase
  have hnonzero : (BDL26CanonicalHistoryMarks.baseInput S 2 sigma).val (r2 S) ≠ 0 :=
    fun hz => hvalue (heval.symm.trans hz)
  exact (BDL26CanonicalHistoryMarks.mem_baseMarks S 2 sigma
    (zVertex S 1 (baseRetainedZ S))).mpr
      (Or.inl ⟨r2 S,base_r2_owner S,hnonzero⟩)
private theorem originalRootPath_semantics (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n)
    (hp : OriginalRootPath S n sigma w) :
    BDL26CanonicalHistoryMarks.root S n ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      w ∈ BDL26CanonicalHistoryMarks.marks S n sigma ∧
      Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma)
        w (BDL26CanonicalHistoryMarks.root S n) := by
  induction hp with
  | rooted hr =>
      exact ⟨hr,hr,Relation.ReflTransGen.refl⟩
  | prepend he _ ih =>
      have hm := (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma _ _).mp he
      exact ⟨ih.1,hm.2.1,(Relation.ReflTransGen.single he).trans ih.2.2⟩
private theorem originalRootPath_prepend_relation (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (hp : Relation.ReflTransGen (BDL26CanonicalHistoryMarks.markedAdjacent S n sigma) u v) :
    OriginalRootPath S n sigma v → OriginalRootPath S n sigma u := by
  induction hp with
  | refl =>
      exact fun hv => hv
  | tail _ he ih =>
      intro hv
      exact ih (@OriginalRootPath.prepend S n sigma _ _ he hv)
private theorem originalRootPath_congr (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    {u v : BDL26CanonicalHistoryMarks.Node S n} (he : u=v)
    (hp : OriginalRootPath S n sigma v) : OriginalRootPath S n sigma u := by
  cases he
  exact hp
private theorem originalRootPath_named_parent (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n) (i : StepIndex (n+2))
    (u : GraphVertex S i.succ.val) (v : GraphVertex S i.castSucc.val)
    (upper lower : BDL26CanonicalHistoryMarks.Node S n)
    (hupper : upper=(⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n))
    (hlower : lower=(⟨i.castSucc,v⟩ : BDL26CanonicalHistoryMarks.Node S n))
    (hparent : parent S i.val u=some v)
    (hmark : upper ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hpath : OriginalRootPath S n sigma lower) :
    OriginalRootPath S n sigma upper := by
  subst upper
  subst lower
  have he : (decodingGraph S (n+2)).adjacent
      (⟨i.succ,u⟩ : BDL26CanonicalHistoryMarks.Node S n) ⟨i.castSucc,v⟩ := by
    apply Or.inr
    apply Or.inr
    refine ⟨i,?_⟩
    simpa only [dif_pos rfl,dif_pos True.intro] using
      (parent_interLevel_iff S (n+2) i v u).mp hparent
  have hmarkLower := (originalRootPath_semantics S n sigma _ hpath).2.1
  have hstep := (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma _ _).mpr
    ⟨he,hmark,hmarkLower⟩
  exact @OriginalRootPath.prepend S n sigma _ _ hstep hpath
private theorem originalRootPath_mem_iff (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (w : BDL26CanonicalHistoryMarks.Node S n) :
    OriginalRootPath S n sigma w ↔
      w ∈ BDL26CanonicalHistoryMarks.rootComponent S n sigma := by
  constructor
  · intro hp
    exact (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mpr
      (originalRootPath_semantics S n sigma w hp)
  · intro hw
    obtain ⟨hr,_hm,hp⟩ := (BDL26CanonicalHistoryMarks.mem_rootComponent S n sigma w).mp hw
    exact originalRootPath_prepend_relation S n sigma w
      (BDL26CanonicalHistoryMarks.root S n) hp (@OriginalRootPath.rooted S n sigma hr)
private theorem originalRootPath_parented_base (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (v : GraphVertex S 2) (hv : v ∈ BDL26CanonicalHistoryMarks.baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    OriginalRootPath S n sigma (BDL26CanonicalHistoryMarks.physicalNode S n 0 v) := by
  have hr := (BDL26CanonicalHistoryMarks.root_marked_iff_parented_base S n sigma).mpr
    ⟨v,hv,u,hp⟩
  have hpath := BDL26CanonicalHistoryMarks.parented_base_root_path S n sigma v hv u hp
  exact originalRootPath_prepend_relation S n sigma _
    (BDL26CanonicalHistoryMarks.root S n) hpath (@OriginalRootPath.rooted S n sigma hr)
private theorem canonical_marked_edge_intro (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (he : (decodingGraph S (n+2)).adjacent u v)
    (hu : u ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hv : v ∈ BDL26CanonicalHistoryMarks.marks S n sigma) :
    BDL26CanonicalHistoryMarks.markedAdjacent S n sigma u v :=
  (BDL26CanonicalHistoryMarks.markedAdjacent_iff S n sigma u v).mpr ⟨he,hu,hv⟩
private theorem originalRootPath_graph_extend (S : OddScale) (n : Nat)
    (sigma : BDL26CanonicalHistoryMarks.Input S n)
    (u v : BDL26CanonicalHistoryMarks.Node S n)
    (he : (decodingGraph S (n+2)).adjacent u v)
    (hu : u ∈ BDL26CanonicalHistoryMarks.marks S n sigma)
    (hv : OriginalRootPath S n sigma v) : OriginalRootPath S n sigma u := by
  have hm := (originalRootPath_semantics S n sigma v hv).2.1
  have he' := canonical_marked_edge_intro S n sigma u v he hu hm
  exact @OriginalRootPath.prepend S n sigma u v he' hv
private theorem actual_base_original_root_path (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S) :
    OriginalRootPath S 2 sigma (actualBaseNode S (zVertex S 1 (baseRetainedZ S))) := by
  have hmarked := actual_base_retained_marked S sigma hbase
  have hpath := originalRootPath_parented_base S 2 sigma
    (zVertex S 1 (baseRetainedZ S)) hmarked
    (zVertex S 0 (seedZ S)) (base_retained_parent S)
  exact originalRootPath_congr S 2 sigma
    (actualBaseNode_physical S (zVertex S 1 (baseRetainedZ S))) hpath
private theorem retained_Z_original_root_path (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2)
    (hbase : BDL26CanonicalHistoryMarks.baseInput S 2 sigma = gamma2 S)
    (hmid : BDL26CanonicalHistoryMarks.inputAt S 2 sigma
      (1 : LevelIndex 2) = lower3 S) :
    OriginalRootPath S 2 sigma (actualMidNode S (zVertex S 2 (r2 S))) := by
  let u : GraphVertex S 3 := zVertex S 2 (r2 S)
  let v : GraphVertex S 2 := zVertex S 1 (baseRetainedZ S)
  have hmarked := actual_mid_Z_marked S sigma hmid
  have hlower := actual_base_original_root_path S sigma hbase
  have hupper := originalRootPath_named_parent S 2 sigma (2 : StepIndex 4) u v
    (actualMidNode S u) (actualBaseNode S v)
    (actualMidNode_literal S u) (actualBaseNode_literal S v)
    (mid_Z_parent S) hmarked hlower
  exact hupper
private theorem actual_retained_original_root_path (S : OddScale) :
    OriginalRootPath S 2 (upper4 S) (actualMidNode S (zVertex S 2 (r2 S))) :=
  retained_Z_original_root_path S (upper4 S) (actual_base_input S) (actual_mid_input S)
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
private theorem rootMask_Q_owner_original_path (S : OddScale) :
    OriginalRootPath S 2 (upper4 S)
      (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S))) := by
  obtain ⟨p,hp⟩ := rootMask_nonzero_Q_coordinate S
  have hm : actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)) ∈
      BDL26CanonicalHistoryMarks.marks S 2 (upper4 S) := by
    rw [← rootMask_Q_coordinate_owner S p]
    apply rootMask_mid_input_owner_marked S p.val
    exact hp
  have he : (decodingGraph S 4).adjacent
      (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)))
      (actualMidNode S (zVertex S 2 (r2 S))) := by
    apply Or.inl
    change (state S 2).presentation.qz (q2 S) (r2 S) = true
    exact q2_incidence S
  exact originalRootPath_graph_extend S 2 (upper4 S)
    (actualMidNode S (@Vertex.q (state S 2).presentation (q2 S)))
    (actualMidNode S (zVertex S 2 (r2 S))) he hm (actual_retained_original_root_path S)
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale)
    (p : LocalRegionIndex ((LQ S).syndromeRegion (q2 S))) :
    rootMaskMidWord S p.val = (lower3 S).val p.val := by
  classical
  let P : FamilyZ S 4 level3 → Prop := fun z => actualMidNode S
    (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z) ∈
      BDL26CanonicalHistoryMarks.rootComponent S 2 (upper4 S)
  let Q : FamilyZ S 4 level3 → Prop := fun z => OriginalRootPath S 2 (upper4 S)
    (actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z))
  have hwhole := @selectedWord_congr_iff (FamilyZ S 4 level3) P Q
    (inferInstance : DecidablePred P) (inferInstance : DecidablePred Q)
    (fun z => (originalRootPath_mem_iff S 2 (upper4 S)
      (actualMidNode S (BDL26CanonicalHistoryMarks.syndromeOwner S 2 (0 : StepIndex 2) z))).symm)
    (lower3 S).val
  have hpath : Q p.val := originalRootPath_congr S 2 (upper4 S)
    (congrArg (actualMidNode S) (rootMask_Q_coordinate_owner S p))
    (rootMask_Q_owner_original_path S)
  have hsemantic := @selectedWord_preserves (FamilyZ S 4 level3) Q
    (inferInstance : DecidablePred Q) (lower3 S).val p.val (fun _ => hpath)
  have horiginal : rootMaskMidWord S p.val = selectedWord P (lower3 S).val p.val :=
    (mask_filter_apply P (lower3 S).val p.val).trans
      (selectedWord_apply P (lower3 S).val p.val).symm
  exact horiginal.trans ((congrFun hwhole p.val).trans hsemantic)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
