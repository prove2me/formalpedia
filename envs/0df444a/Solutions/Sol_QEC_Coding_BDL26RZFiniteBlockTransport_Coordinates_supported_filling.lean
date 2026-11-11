-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.supported_filling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:46:59.959551+00:00
-- url     : https://prove2.me/submissions/058e9936-8aa0-42ad-bf50-b69fc63ce2ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
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
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzLocal_cycle_of_cocycle_q_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQEdge_coboundary_apply_q
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_has_qFillings
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_tannerCoboundary_squared
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_zCylinder_cycle_has_filling
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
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzFace_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map2Coord_canonicalBasis
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary0_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_extendRZLocalEdgeWord_eq
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZFaceWord
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCoboundary0_extendRZQEdgeWord
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
private theorem push_supported {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (w : Word (ZMod 2) α)
    (Y : Finset β) (hf : ∀ a, f a ∈ Y) :
    hammingSupport (wordPushforward f w) ⊆ Y := by
  apply supported
  intro x hx
  rw [wordPushforward_apply]
  apply Finset.sum_eq_zero
  intro a _
  exact if_neg (fun he => hx (by simpa only [he] using hf a))
namespace Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
private theorem qPotential_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (q : P.Q) (hq : q ∈ Q0)
    (e : Word BDL26FiniteTannerSquare.Field (QDoubleCylinderEdge (transposePresentation P) q S)) :
    hammingSupport (extendRZQEdgeWord P S q e) ⊆ potentialStar P S Q0 Z0 := by
  apply push_supported
  intro a
  simp [rzMap1QEdgeX,potentialStar,hq]
private theorem zPotential_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (z : P.Z) (hz : z ∈ zplus P Q0 Z0)
    (f : Word BDL26FiniteTannerSquare.Field (ZDoubleCylinderFace P z S)) :
    hammingSupport (extendRZFaceWord P S z f) ⊆ potentialStar P S Q0 Z0 := by
  apply push_supported
  intro a
  simp [potentialStar,hz]
private theorem qVertex_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (q : P.Q) (hq : q ∈ Q0)
    (w : Word BDL26FiniteTannerSquare.Field
      (QDoubleCylinderVertex (transposePresentation P) q S)) :
    hammingSupport (extendRZQVertexWord P S q w) ⊆ star P S Q0 Z0 := by
  change hammingSupport (wordPushforward
    (fun v => (Sum.inr ⟨q,v⟩ : RZQ P S)) w) ⊆ star P S Q0 Z0
  apply push_supported
  intro v
  exact (mem_input_q P S Q0 (zplus P Q0 Z0) q v).mpr hq
private theorem qPotential_boundary_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (q : P.Q) (hq : q ∈ Q0)
    (e : Word BDL26FiniteTannerSquare.Field (QDoubleCylinderEdge (transposePresentation P) q S)) :
    hammingSupport (rzCoboundary0 P A S (extendRZQEdgeWord P S q e)) ⊆ star P S Q0 Z0 := by
  apply supported
  intro p hp
  have h := congrFun (rzCoboundary0_extendRZQEdgeWord P A S q e) p
  rw [h]
  simp only [Pi.add_apply,Finset.sum_apply]
  have hqzero : extendRZQVertexWord P S q
      (graphBoundary (qDoubleCylinderEdgeStart (transposePresentation P) q S)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S) e) p=0 := by
    exact zero_off _ _ (qVertex_support P S Q0 Z0 q hq _) p hp
  rw [hqzero,zero_add]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hqz : P.qz q z=true
  · rw [dif_pos hqz,extendRZLocalEdgeWord_eq]
    apply BDL26RZSupportedBoundary.extendEdge_supported
    intro hin
    apply hp
    have hz : z ∈ zplus P Q0 Z0 := Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,q,hq,hqz⟩)
    have ho : rzCorrectionOwner P S p=Vertex.z z :=
      (Finset.mem_filter.mp hin).2
    rcases p with ⟨z',edge⟩ | ⟨q',vertex⟩
    · have he : z'=z := Vertex.z.inj ho
      exact (mem_input_z P S _ _ _ _).mpr (he.symm ▸ hz)
    · exact False.elim (by
        change Vertex.q q'=Vertex.z z at ho
        cases ho)
  · rw [dif_neg hqz]
    rfl
end Coordinates
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)
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
open QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
namespace QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
theorem _root_.solution (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (w : Word BDL26FiniteTannerSquare.Field (RZQ P S)) (hc : rzCoboundary1 P A S w=0)
    (hp : rzQParity P S w=0) (hw : hammingSupport w ⊆ star P S Q0 Z0) :
    ∃ p : Word BDL26FiniteTannerSquare.Field (RZX P S), rzCoboundary0 P A S p=w ∧
      hammingSupport p ⊆ potentialStar P S Q0 Z0 := by
  obtain ⟨edges,he⟩ := Classical.skolem.mp
    (rzQParity_zero_has_qFillings P A.toTannerSquareAdmissible S w hp)
  let pq := ∑ q ∈ Q0, extendRZQEdgeWord P S q (edges q)
  have hpqs : hammingSupport pq ⊆ potentialStar P S Q0 Z0 :=
    sum_supported Q0 _ _ (fun q hq => qPotential_support P S Q0 Z0 q hq _)
  have hdqs : hammingSupport (rzCoboundary0 P A S pq) ⊆ star P S Q0 Z0 := by
    dsimp only [pq]
    rw [map_sum]
    exact sum_supported Q0 _ _ (fun q hq => qPotential_boundary_support P S A Q0 Z0 q hq _)
  have hq (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
      rzCoboundary0 P A S pq (.inr ⟨q,v⟩)=w (.inr ⟨q,v⟩) := by
    dsimp only [pq]
    rw [map_sum]
    simp only [Finset.sum_apply,rzQEdge_coboundary_apply_q,he]
    by_cases hmem : q ∈ Q0
    · rw [Finset.sum_eq_single q]
      · simp [extendRZQVertexWord,wordPushforward_apply]
      · intro q' _ hne
        simp [extendRZQVertexWord,wordPushforward_apply,hne,Ne.symm hne,Sigma.mk.injEq]
      · simp [hmem]
    · have hwq : w (.inr ⟨q,v⟩)=0 := zero_off w _ hw _ (by simpa [star] using hmem)
      rw [hwq]
      apply Finset.sum_eq_zero
      intro q' hq'
      have hne : q≠q' := fun hh => hmem (by simpa only [hh] using hq')
      simp [extendRZQVertexWord,wordPushforward_apply,hne,Ne.symm hne,Sigma.mk.injEq]
  let r := w+rzCoboundary0 P A S pq
  have hrs : hammingSupport r ⊆ star P S Q0 Z0 := add_supported _ _ _ hw hdqs
  have hrq (q : P.Q) (v : QDoubleCylinderVertex (transposePresentation P) q S) :
      r (.inr ⟨q,v⟩)=0 := by
    simp only [r,Pi.add_apply,hq]
    exact CharTwo.add_self_eq_zero _
  have hrc : rzCoboundary1 P A S r=0 := by
    dsimp only [r]
    rw [map_add,hc,zero_add]
    exact LinearMap.congr_fun
      (tannerCoboundary_squared (rzReplacementPresentation P A.toTannerSquareAdmissible S)) pq
  have hf (z : P.Z) : ∃ f : Word BDL26FiniteTannerSquare.Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S f=
        fun e => r (.inl ⟨z,e⟩) :=
    zCylinder_cycle_has_filling P A.toTannerSquareAdmissibleV3 R z S _
      (rzLocal_cycle_of_cocycle_q_zero P A S r hrc hrq z)
  choose faces hfaces using hf
  let pz := ∑ z ∈ zplus P Q0 Z0, extendRZFaceWord P S z (faces z)
  have hpzs : hammingSupport pz ⊆ potentialStar P S Q0 Z0 :=
    sum_supported _ _ _ (fun z hz => zPotential_support P S Q0 Z0 z hz _)
  have hpz : rzCoboundary0 P A S pz=r := by
    dsimp only [pz]
    rw [map_sum]
    simp only [rzCoboundary0_extendRZFaceWord,extendRZLocalEdgeWord_eq,hfaces]
    funext p
    rw [Finset.sum_apply]
    rcases p with ⟨z,e⟩ | ⟨q,v⟩
    · by_cases hz : z ∈ zplus P Q0 Z0
      · rw [Finset.sum_eq_single z]
        · simp [extendZEdgeWord]
        · intro z' _ hne
          simp [extendZEdgeWord,Ne.symm hne]
        · simp [hz]
      · rw [zero_off r _ hrs _ (by simpa [star] using hz)]
        apply Finset.sum_eq_zero
        intro z' hz'
        have hne : z≠z' := fun hh => hz (by simpa only [hh] using hz')
        simp [extendZEdgeWord,hne]
    · simp only [extendZEdgeWord,Finset.sum_const_zero,hrq]
  refine ⟨pz+pq,?_,add_supported _ _ _ hpzs hpqs⟩
  rw [map_add,hpz]
  dsimp only [r]
  rw [add_assoc,twice,add_zero]
end QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
