-- Prove2me | solution 1 for QEC.Coding.BDL26RXQBlockTransport.correction_add_map1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:55:50.507059+00:00
-- url     : https://prove2.me/submissions/19340f94-d8d1-489d-9640-3552afde09d0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incoming_one_x
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incoming_one_q
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
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_equiv_mk
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_components
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qCorrectionEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSyndromeEquiv_val
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_regionExtension_apply
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_correction_sum
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
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rxXiSignal_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_cx_component_invariant
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_q_component_invariant
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
namespace QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
private theorem word_add_self {ι : Type*} (w : Word BDL26Field ι) : w+w=0 := by
  funext p
  exact CharTwo.add_self_eq_zero (w p)
private theorem eq_of_word_add_zero {ι : Type*} (u v : Word BDL26Field ι)
    (h : u+v=0) : u=v := by
  have he := congrArg (fun t => u+t) h
  rw [← add_assoc, word_add_self, zero_add, add_zero] at he
  exact he.symm
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
private theorem selected_rx :
    (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl
private theorem xi_eq_x (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (x : XCoord S i) :
    rxXiSignal (Data S depth i h) s (.inl x) 1 =
      rxXiSignal (Data S depth i h) t (.inl x) 1 := by
  funext p
  rw [rxXiSignal_apply, rxXiSignal_apply]
  by_cases hd : (Data S depth i h).levelGraph.graph.distance
      ((Data S depth i h).topCenter p) (.inl x) ≤ ((1 : Nat) : WithTop Nat)
  · rw [if_pos hd, if_pos hd]
    have hc := incoming_one_x S depth i h x _
      (by simpa only [Nat.cast_one, WithTop.coe_one] using hd)
    have hp := ((Data S depth i h).topCenter_x_iff x p).mpr hc
    exact congrFun (hx x) ⟨p,hp⟩
  · rw [if_neg hd, if_neg hd]
private theorem xi_eq_q (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (q : QCoord S i)
    (hq : restrictWordLinear ((rxLq S depth i h).syndromeRegion q) s =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) t) :
    rxXiSignal (Data S depth i h) s (.inr (.inl q)) 1 =
      rxXiSignal (Data S depth i h) t (.inr (.inl q)) 1 := by
  funext p
  rw [rxXiSignal_apply, rxXiSignal_apply]
  by_cases hd : (Data S depth i h).levelGraph.graph.distance
      ((Data S depth i h).topCenter p) (.inr (.inl q)) ≤ ((1 : Nat) : WithTop Nat)
  · rw [if_pos hd, if_pos hd]
    rcases incoming_one_q S depth i h q _
      (by simpa only [Nat.cast_one, WithTop.coe_one] using hd) with hc | ⟨x,hc,_⟩
    · exact congrFun hq ⟨p, ((Data S depth i h).topCenter_q_iff q p).mpr hc⟩
    · exact congrFun (hx x) ⟨p, ((Data S depth i h).topCenter_x_iff x p).mpr hc⟩
  · rw [if_neg hd, if_neg hd]
private theorem cx_eq_of_reads (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (x : XCoord S i) :
    cxComponentTotal (Data S depth i h) s x = cxComponentTotal (Data S depth i h) t x := by
  calc
    _ = cxComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) s (.inl x) 1) x :=
      rx_cx_component_invariant _ _ _
    _ = cxComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) t (.inl x) 1) x := by
      rw [xi_eq_x S depth i h s t hx x]
    _ = _ := (rx_cx_component_invariant _ _ _).symm
private theorem cq_eq_of_reads (s t : Syn S depth i)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) s =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) t)
    (q : QCoord S i)
    (hq : restrictWordLinear ((rxLq S depth i h).syndromeRegion q) s =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) t) :
    cqComponentTotal (Data S depth i h) s q = cqComponentTotal (Data S depth i h) t q := by
  calc
    _ = cqComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) s (.inr (.inl q)) 1) q :=
      rx_q_component_invariant _ _ _
    _ = cqComponentTotal (Data S depth i h)
        (rxXiSignal (Data S depth i h) t (.inr (.inl q)) 1) q := by
      rw [xi_eq_q S depth i h s t hx q hq]
    _ = _ := (rx_q_component_invariant _ _ _).symm
private theorem map2_x_zero (s : (indexedFamily S depth).Cochain2 i.castSucc)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).selectedMap i).map2 s)=0 := by
  rw [selected_rx]
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.1) _ hz
  rw [(Data S depth i h).xSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.property⟩
private theorem map2_q_zero (s : (indexedFamily S depth).Cochain2 i.castSucc)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (((indexedDecoderData S depth).selectedMap i).map2 s)=0 := by
  rw [selected_rx]
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.2) _ hz
  rw [(Data S depth i h).qSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, p.property⟩
private theorem shift_syndrome_difference (a : Upper S depth i) (w : Lower S depth i) :
    (errorSyndrome S depth i a).val +
      (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val =
      ((indexedDecoderData S depth).selectedMap i).map2
        ((indexedFamily S depth).coboundary1 i.castSucc w) := by
  change (indexedFamily S depth).coboundary1 i.succ a +
      (indexedFamily S depth).coboundary1 i.succ
        (a+((indexedDecoderData S depth).selectedMap i).map1 w) = _
  rw [map_add, ← add_assoc, word_add_self, zero_add]
  exact LinearMap.congr_fun
    (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1) w
private theorem shift_x_agreement (a : Upper S depth i) (w : Lower S depth i)
    (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
        (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val := by
  apply eq_of_word_add_zero
  rw [← map_add, shift_syndrome_difference, map2_x_zero]
private theorem shift_q_agreement (a : Upper S depth i) (w : Lower S depth i)
    (q : QCoord S i) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        (errorSyndrome S depth i (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val := by
  apply eq_of_word_add_zero
  rw [← map_add, shift_syndrome_difference, map2_q_zero]
end QEC.Coding.BDL26RXQBlockTransport
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXQBlockTransport
theorem _root_.solution (a : Upper S depth i) (w : Lower S depth i) :
    (run S depth i h (a+((indexedDecoderData S depth).selectedMap i).map1 w)).correction =
      (run S depth i h a).correction := by
  have hx := shift_x_agreement S depth i h a w
  have hq := shift_q_agreement S depth i h a w
  rw [run, run, rxStepOutput_correction_sum, rxStepOutput_correction_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    exact (cx_eq_of_reads S depth i h _ _ hx x).symm
  · apply Finset.sum_congr rfl
    intro q _
    exact (cq_eq_of_reads S depth i h _ _ hx q (hq q)).symm
end QEC.Coding.BDL26RXQBlockTransport
