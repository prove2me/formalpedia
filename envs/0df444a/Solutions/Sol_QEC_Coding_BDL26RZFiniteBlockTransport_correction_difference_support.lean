-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.correction_difference_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:36:54.473425+00:00
-- url     : https://prove2.me/submissions/7b46e2c7-1fee-4ffb-99ce-c80b2672f053

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_syndrome_support
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_zBlock_eq_correctionRegion
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_delta1_coordinates
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_generator_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_value
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixCocycle_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_equiv_mk
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
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_equiv_symm_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzData_coordinates
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_fiberPart_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxQOutgoing_nonincident
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_equivalence_classOf
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_equivalence_symm_apply
import Theorems.Thm_QEC_Coding_BDL26SeedCohomology_stateZeroEquivalence_classOf
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
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_copiedQ_image_vertical
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_copy
import Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_verticalZ_image_vertical
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedLeafAdapters_rzOutput_correction
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_coe
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_supported
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_zero
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.generator_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_value
attribute [local simp] QEC.Coding.BDL26FiniteCohomology.prefixCocycle_zero
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXCohomology.equiv_mk
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
attribute [local simp] QEC.Coding.BDL26RZCohomology.backward_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.equiv_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.equiv_symm_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.forward_mk
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
attribute [local simp] QEC.Coding.BDL26SeedCohomology.equivalence_classOf
attribute [local simp] QEC.Coding.BDL26SeedCohomology.equivalence_symm_apply
attribute [local simp] QEC.Coding.BDL26SeedCohomology.stateZeroEquivalence_classOf
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
noncomputable section
namespace QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
private theorem twice {α : Type*} (w : Word (ZMod 2) α) : w+w=0 := by
  funext x
  exact CharTwo.add_self_eq_zero _
private theorem zero_off {α : Type*} [Fintype α]
    (w : Word (ZMod 2) α) (Y : Finset α) (h : hammingSupport w ⊆ Y)
    (x : α) (hx : x ∉ Y) : w x=0 := by
  by_contra hn
  exact hx (h (by simpa [hammingSupport] using hn))
private theorem supported {α : Type*} [Fintype α]
    (w : Word (ZMod 2) α) (Y : Finset α) (h : ∀ x, x ∉ Y → w x=0) :
    hammingSupport w ⊆ Y := by
  intro x hx
  by_contra hn
  exact (show w x≠0 by simpa [hammingSupport] using hx) (h x hn)
private theorem add_supported {α : Type*} [Fintype α]
    (a b : Word (ZMod 2) α) (Y : Finset α)
    (ha : hammingSupport a ⊆ Y) (hb : hammingSupport b ⊆ Y) :
    hammingSupport (a+b) ⊆ Y := by
  apply supported
  intro x hx
  simp only [Pi.add_apply,zero_off a Y ha x hx,zero_off b Y hb x hx,zero_add]
private theorem sum_supported {α β : Type*} [Fintype β]
    (J : Finset α) (f : α → Word (ZMod 2) β) (Y : Finset β)
    (hf : ∀ a ∈ J, hammingSupport (f a) ⊆ Y) :
    hammingSupport (∑ a ∈ J, f a) ⊆ Y := by
  apply supported
  intro x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun a ha => zero_off _ _ (hf a ha) x hx)
namespace Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
private theorem zBlocks_mono (Z0 Z1 : Finset P.Z) (h : Z0 ⊆ Z1) :
    zBlocks P S Z0 ⊆ zBlocks P S Z1 := by
  intro p hp
  rcases p with ⟨z,e⟩ | ⟨q,v⟩
  · exact (mem_zBlocks_z P S _ _ _).mpr (h ((mem_zBlocks_z P S _ _ _).mp hp))
  · exact False.elim (by simpa only [zBlocks,Finset.mem_filter,Finset.mem_univ,true_and] using hp)
end Coordinates
private theorem reindex_membership {ι α β : Type} (h : α=β)
    (f : ι → Finset α) (g : ι → Finset β) (he : HEq f g) (z : ι) (x : α) :
    x ∈ f z ↔ Equiv.cast h x ∈ g z := by cases h; rw [eq_of_heq he]; rfl
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
private theorem read_support {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (f : Word BDL26FiniteTannerSquare.Field α → Word BDL26FiniteTannerSquare.Field β)
    (hf : ∀ w x, f w x=w (e.symm x)) (w : Word BDL26FiniteTannerSquare.Field α) (Y : Finset β) :
    hammingSupport (f w) ⊆ Y ↔
      hammingSupport w ⊆ Finset.univ.filter (fun x => e x ∈ Y) := by
  constructor
  · intro h x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,h ?_⟩
    simpa [hammingSupport,hf] using hx
  · intro h x hx
    have hh := h (show e.symm x ∈ hammingSupport w by simpa [hammingSupport,hf] using hx)
    simpa using (Finset.mem_filter.mp hh).2
private theorem read_input_support (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (w : Upper S depth i) :
    hammingSupport (read1 S depth i odd w) ⊆ Coordinates.inputBlocks (Old S depth i) S Q0 Z0 ↔
      hammingSupport w ⊆ inputBlocks S depth i odd Q0 Z0 := by
  rw [read_support _ _ (read1_apply S depth i odd)]
  have hset : (Finset.univ.filter fun p => coord1 S depth i odd p ∈
      Coordinates.inputBlocks (Old S depth i) S Q0 Z0)=inputBlocks S depth i odd Q0 Z0 := by
    ext p
    simp [inputBlocks,qBlocks,zBlocks,Coordinates.inputBlocks]
  rw [hset]
private theorem run_components (a : Upper S depth i) :
    (run S depth i odd a).correction=∑ z,
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i a).val := by
  exact AuditedLeafAdapters.rzOutput_correction
    (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
    (rzData_inducedCoboundaryCompatibility S depth i odd)
    (by change (i.val+1)%2=0; omega) (errorSyndrome S depth i a)
private theorem exact_residual_agreement (z : (Old S depth i).Z)
    (a b : Upper S depth i)
    (h : ∀ p ∈ (rzData S depth i odd).coarseRegion z,
      (errorSyndrome S depth i a).val p=(errorSyndrome S depth i b).val p) :
    localResidual (rzData S depth i odd) z (errorSyndrome S depth i a).val=
      localResidual (rzData S depth i odd) z (errorSyndrome S depth i b).val := by
  have ht : topParity (rzData S depth i odd) (errorSyndrome S depth i a).val z=
      topParity (rzData S depth i odd) (errorSyndrome S depth i b).val z :=
    Finset.sum_congr rfl h
  have hm : maskWord ((rzData S depth i odd).coarseRegion z) (errorSyndrome S depth i a).val=
      maskWord ((rzData S depth i odd).coarseRegion z) (errorSyndrome S depth i b).val := by
    funext p
    by_cases hp : p ∈ (rzData S depth i odd).coarseRegion z
    · simp only [maskWord,if_pos hp,h p hp]
    · simp only [maskWord,if_neg hp]
  unfold localResidual
  rw [hm,ht]
private theorem region_syndrome_coordinate (z : (Old S depth i).Z)
    (p : FamilyZ S depth i.succ) :
    p ∈ (rzData S depth i odd).coarseRegion z ↔ (coord2 S depth i odd p).1=z := by
  have hc : p ∈ (rzData S depth i odd).coarseRegion z ↔
      coord2 S depth i odd p ∈ BDL26RZConcreteParity.blockRegion (Old S depth i) S z :=
    reindex_membership (congrArg TannerSquarePresentation.Z (upper_eq S depth i odd))
      _ _ (rzData_coordinates S depth i odd).1 z p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp (hc.mp hp)).2
  · intro hp
    exact hc.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
section TopHistory
open BDL26OwnerIncidenceMasks BDL26CanonicalHistoryMarks
end TopHistory
section ConstructorWitness
end ConstructorWitness
end QEC.Coding.BDL26RZFiniteBlockTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
namespace QEC.Coding.BDL26RZFiniteBlockTransport
theorem _root_.solution (Q0 : Finset (Old S depth i).Q)
    (Z0 : Finset (Old S depth i).Z) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ inputBlocks S depth i odd Q0 Z0) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by
  have hs := Coordinates.syndrome_support (Old S depth i) S (state S i.val).admissible Q0 Z0
    (read1 S depth i odd (a+b)) ((read_input_support S depth i odd Q0 Z0 _).mpr he)
  have agree (z : (Old S depth i).Z) (hz : z ∉ Coordinates.zplus (Old S depth i) Q0 Z0) :
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i a).val=
      localCorrectionComponent (rzData S depth i odd) (rzData_localTopCohomology S depth i odd)
        z (errorSyndrome S depth i b).val := by
    unfold localCorrectionComponent
    rw [exact_residual_agreement S depth i odd z a b (by
      intro p hp
      have hz' := (region_syndrome_coordinate S depth i odd z p).mp hp
      have hzero := zero_off _ _ hs (coord2 S depth i odd p) (by
        simpa [Coordinates.syndromeBlocks,hz'] using hz)
      rw [← delta1_coordinates] at hzero
      simp only [read2_apply,Equiv.symm_apply_apply,map_add,Pi.add_apply] at hzero
      have hh := congrArg (fun t : BDL26FiniteTannerSquare.Field => t+(indexedFamily S depth).coboundary1 i.succ b p) hzero
      change ((indexedFamily S depth).coboundary1 i.succ a) p=
        ((indexedFamily S depth).coboundary1 i.succ b) p
      simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,zero_add] using hh)]
  rw [run_components,run_components,← Finset.sum_add_distrib]
  apply sum_supported
  intro z _
  by_cases hz : z ∈ Coordinates.zplus (Old S depth i) Q0 Z0
  · have hpart (w : Upper S depth i) :
        hammingSupport (localCorrectionComponent (rzData S depth i odd)
          (rzData_localTopCohomology S depth i odd) z (errorSyndrome S depth i w).val) ⊆
        zBlocks S depth i odd {z} := by
      apply supported
      intro p hp
      apply localCorrectionComponent_supported
      simpa only [← zBlock_eq_correctionRegion S depth i odd z] using hp
    have hmono : zBlocks S depth i odd {z} ⊆
        zBlocks S depth i odd (Coordinates.zplus (Old S depth i) Q0 Z0) := by
      intro p hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply Coordinates.zBlocks_mono _ S {z} _ (Finset.singleton_subset_iff.mpr hz)
      exact (Finset.mem_filter.mp hp).2
    exact add_supported _ _ _ ((hpart a).trans hmono) ((hpart b).trans hmono)
  · rw [agree z hz,twice]
    simp [hammingSupport]
end QEC.Coding.BDL26RZFiniteBlockTransport
