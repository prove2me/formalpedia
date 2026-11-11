-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.setup_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:17:00.244037+00:00
-- url     : https://prove2.me/submissions/523b4b65-f479-4716-ae4b-117dfd3a07b9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_mapQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_filterQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_rangeQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_anyQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xqQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qzQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_faceAtQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_dedupQ_length_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_carrier_counts
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_generate_cost
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_x
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_z
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_hermitian
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_syndromeRegion_mem
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_nextState_qubit_card_lower
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
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_input_labels_le_qubits
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
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
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
namespace QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
private theorem filterQ_length {A : Type*} (p : A → Query Bool) (as : List A) :
    (filterQ p as).1.length≤ as.length := by
  rw [filterQ_value]
  exact List.length_filter_le _ _
private theorem memCodeQ_cost (c : Code) (as : List Code) :
    (memCodeQ c as).2=42*as.length :=
  anyQ_cost _ _ 41 (by intro a ha; rfl)
private theorem dedupQ_cost (as : List Code) : (dedupQ as).2≤44*(as.length+1)^2 := by
  induction as with
  | nil => simp [dedupQ]
  | cons a as ih =>
      have hl := dedupQ_length_le as
      simp only [dedupQ,memCodeQ_cost,List.length_cons]
      nlinarith
private theorem radius_components (F : Frame) (m : ℕ) :
    F.nx+1≤ radius F m ∧ F.nq+1≤ radius F m ∧ F.nz+1≤ radius F m ∧
    F.nf+1≤ radius F m ∧ F.faces.length+1≤ radius F m ∧ m+1≤ radius F m := by
  simp only [radius,frameSize]
  omega
private theorem work_length {A : Type*} (q : Query (List A)) : q.1.length≤ work q := by
  unfold work
  omega
private theorem work_mono_value_cost {A : Type*} (a b : Query (List A))
    (hv : a.1=b.1) (hc : a.2≤b.2) : work a≤work b := by
  change a.1.length+a.2+1≤b.1.length+b.2+1
  rw [hv]
  exact Nat.add_le_add_right (Nat.add_le_add_left hc b.1.length) 1
private theorem work_cost {A : Type*} (q : Query (List A)) : q.2≤ work q := by simp [work]; omega
private theorem pow_mono (R : ℕ) (hR : 1≤ R) {a b : ℕ} (h : a≤ b) : R^a≤ R^b :=
  Nat.pow_le_pow_right hR h
private theorem pow_one_le (R d : ℕ) (hR : 1≤ R) : 1≤ R^d := by
  simpa using pow_mono R hR (show 0≤ d from Nat.zero_le _)
private theorem pow_constant (R d k c : ℕ) (hR : 2≤ R) (hc : c≤2^k) :
    c*R^d≤ R^(d+k) := by
  have hk : c≤ R^k := hc.trans (Nat.pow_le_pow_left hR k)
  calc
    c*R^d ≤ R^k*R^d := Nat.mul_le_mul_right (R^d) hk
    _ = R^(d+k) := by rw [pow_add]; exact Nat.mul_comm _ _
private theorem pow_sum (R d : ℕ) (hR : 2≤ R) {a b : ℕ}
    (ha : a≤ R^d) (hb : b≤ R^d) : a+b≤ R^(d+1) := by
  have := pow_constant R d 1 2 hR (by decide)
  omega
private theorem mapQ_work {A B : Type*} (f : A → Query B) (as : List A) (C : ℕ)
    (hf : ∀a∈as,(f a).2≤ C) : work (mapQ f as)≤(as.length+1)*(C+3) := by
  have hc := mapQ_cost_le f as C hf
  rw [work,mapQ_length]
  nlinarith
private theorem filterQ_work {A : Type*} (p : A → Query Bool) (as : List A) (C : ℕ)
    (hp : ∀a∈as,(p a).2≤ C) : work (filterQ p as)≤(as.length+1)*(C+3) := by
  have hc := filterQ_cost_le p as C hp
  have hl := filterQ_length p as
  unfold work
  nlinarith
private theorem flatMapQ_work {A B : Type*} (f : A → Query (List B)) (as : List A) (C : ℕ)
    (hf : ∀a∈as,work (f a)≤ C) : work (flatMapQ f as)≤2*as.length*C+1 := by
  induction as with
  | nil => simp [flatMapQ,work]
  | cons a as ih =>
      have ha := hf a (by simp)
      have ht := ih (fun b hb => hf b (by simp [hb]))
      simp only [flatMapQ,appendQ,work,List.length_append,List.length_cons] at ha ht ⊢
      nlinarith
private theorem map_pow {A B : Type*} (R : ℕ) (hR : 2≤ R) (a b : ℕ)
    (f : A → Query B) (as : List A) (ha : as.length≤ R^a)
    (hf : ∀x∈as,(f x).2≤ R^b) : work (mapQ f as)≤ R^(a+b+3) := by
  have h := mapQ_work f as (R^b) hf
  have h1 := pow_one_le R a (by omega)
  have h2 := pow_one_le R b (by omega)
  have hp := pow_constant R (a+b) 3 8 hR (by decide)
  calc
    work (mapQ f as) ≤ (as.length+1)*(R^b+3) := h
    _ ≤ (2*R^a)*(4*R^b) := Nat.mul_le_mul (by omega) (by omega)
    _ = 8*R^(a+b) := by rw [pow_add]; ring
    _ ≤ R^(a+b+3) := hp
private theorem filter_pow {A : Type*} (R : ℕ) (hR : 2≤ R) (a b : ℕ)
    (f : A → Query Bool) (as : List A) (ha : as.length≤ R^a)
    (hf : ∀x∈as,(f x).2≤ R^b) : work (filterQ f as)≤ R^(a+b+3) := by
  have h := filterQ_work f as (R^b) hf
  have h1 := pow_one_le R a (by omega)
  have h2 := pow_one_le R b (by omega)
  calc
    work (filterQ f as) ≤ (as.length+1)*(R^b+3) := h
    _ ≤ (2*R^a)*(4*R^b) := Nat.mul_le_mul (by omega) (by omega)
    _ = 8*R^(a+b) := by rw [pow_add]; ring
    _ ≤ R^(a+b+3) := pow_constant R (a+b) 3 8 hR (by decide)
private theorem flat_pow {A B : Type*} (R : ℕ) (hR : 2≤ R) (a b : ℕ)
    (f : A → Query (List B)) (as : List A) (ha : as.length≤ R^a)
    (hf : ∀x∈as,work (f x)≤ R^b) : work (flatMapQ f as)≤ R^(a+b+3) := by
  have h := flatMapQ_work f as (R^b) hf
  have h1 := pow_one_le R (a+b) (by omega)
  have hm := Nat.mul_le_mul_right (R^b) ha
  calc
    work (flatMapQ f as) ≤ 2*as.length*R^b+1 := h
    _ = 2*(as.length*R^b)+1 := by rw [Nat.mul_assoc]
    _ ≤ 2*(R^a*R^b)+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hm) 1
    _ ≤ 4*(R^a*R^b) := by
      simpa only [pow_add] using (show 2*R^(a+b)+1≤4*R^(a+b) by omega)
    _ = 4*R^(a+b) := by rw [pow_add]
    _ ≤ R^(a+b+2) := pow_constant R (a+b) 2 4 hR (by decide)
    _ ≤ R^(a+b+3) := pow_mono R (by omega) (by omega)
private theorem range_pow (R : ℕ) (hR : 2≤ R) (n : ℕ) (hn : n≤ R) :
    work (rangeQ n)≤ R^7 := by
  have hc := rangeQ_cost_le n
  have h1 : 1≤ R := by omega
  have hn1 : n+1≤ 2*R := by omega
  have hs := Nat.mul_le_mul hn1 hn1
  have hr2 : R≤ R^2 := by simpa only [pow_one] using pow_mono R h1 (by decide : 1≤2)
  have h2 := pow_one_le R 2 h1
  calc
    work (rangeQ n) = n+(rangeQ n).2+1 := by rw [work,rangeQ_value,List.length_range]
    _ ≤ n+4*(n+1)^2+1 := by omega
    _ ≤ 32*R^2 := by nlinarith only [hn,hs,hr2,h2]
    _ ≤ R^7 := pow_constant R 2 5 32 hR (by decide)
private theorem attach_work_eq {A : Type*} (q : Query (List A)) (c : ℕ) :
    work (q.1,c+q.2)=work q+c := by
  rcases q with ⟨xs,k⟩
  simp only [work]
  omega
private theorem loop_pow {A : Type*} (R : ℕ) (hR : 2≤ R) (b n : ℕ)
    (hn : n≤ R) (f : ℕ → Query (List A))
    (hf : ∀i< n,work (f i)≤ R^b) : work (loopQ n f)≤ R^(b+10) := by
  have hr := range_pow R hR n hn
  let q := flatMapQ f (rangeQ n).1
  have ho : work q ≤ R^(1+b+3) := flat_pow R hR 1 b f (rangeQ n).1
    (by simpa only [rangeQ_value,List.length_range,pow_one] using hn)
    (by intro i hi; exact hf i (by simpa only [rangeQ_value,List.mem_range] using hi))
  have hq : work q ≤ R^(b+9) := ho.trans (pow_mono R (by omega) (by omega))
  have hc : (rangeQ n).2 ≤ R^(b+9) :=
    (work_cost _).trans (hr.trans (pow_mono R (by omega) (by omega)))
  have hs := pow_sum R (b+9) hR hq hc
  have he : b+9+1=b+10 := by omega
  rw [he] at hs
  change work (q.1,(rangeQ n).2+q.2) ≤ R^(b+10)
  rw [attach_work_eq]
  exact hs
private theorem collect_pow {A : Type*} (R : ℕ) (hR : 2≤ R) (a b : ℕ)
    (qs : List (Query (List A))) (ha : qs.length≤ R^a)
    (hb : ∀q∈qs,work q≤ R^b) : work (collectQ qs)≤ R^(a+b+3) :=
  flat_pow R hR a b id qs ha hb
private theorem singleton_pow (R : ℕ) (hR : 2≤ R) (c : Code) :
    work (singletonQ c)≤ R^6 := by
  exact (show 35≤2^6 by decide).trans (Nat.pow_le_pow_left hR 6)
private theorem attach_pow {A : Type*} (R : ℕ) (hR : 2≤ R) (a : ℕ)
    (q : Query (List A)) (c : ℕ) (hq : work q≤ R^a) (hc : c≤ R^a) :
    work (q.1,c+q.2)≤ R^(a+1) := by
  rw [attach_work_eq]
  exact pow_sum R a hR hq hc
private theorem attach_fixed {A : Type*} (R : ℕ) (hR : 2≤ R) (a k : ℕ)
    (q : Query (List A)) (c : ℕ) (hq : work q≤ R^a) (hc : c≤2^k*R^a) :
    work (q.1,c+q.2)≤ R^(a+k+1) := by
  have hk : 1≤ 2^k := Nat.one_le_pow k 2 (by decide)
  have hp := pow_constant R a (k+1) (2^k+1) hR (by rw [pow_succ]; omega)
  calc
    work (q.1,c+q.2) = work q+c := attach_work_eq q c
    _ ≤ R^a+2^k*R^a := Nat.add_le_add hq hc
    _ = (2^k+1)*R^a := by ring
    _ ≤ R^(a+k+1) := by simpa only [Nat.add_assoc] using hp
private theorem radius_two (F : Frame) (m : ℕ) : 2≤ radius F m := by
  simp only [radius,frameSize]; omega
private theorem relax {A : Type*} (R : ℕ) (hR : 2≤ R) {a b : ℕ}
    (hab : a≤ b) {q : Query (List A)} (hq : work q≤ R^a) : work q≤ R^b :=
  hq.trans (pow_mono R (by omega) hab)
private theorem dedup_pow (R : ℕ) (hR : 2≤ R) (a : ℕ) (xs : List Code)
    (hx : xs.length≤ R^a) : work (dedupQ xs)≤ R^(2*a+10) := by
  have hl := dedupQ_length_le xs
  have hc := dedupQ_cost xs
  have h1 := pow_one_le R a (by omega)
  have hp := pow_constant R (2*a) 10 1024 hR (by decide)
  have he : R^(2*a)=(R^a)^2 := by rw [two_mul,pow_add,pow_two]
  rw [he] at hp
  unfold work
  nlinarith
private theorem actual_frame_size (S : OddScale) (n : ℕ) :
    frameSize (generateQ S n).1≤130*Fintype.card (state S n).presentation.Q+1 := by
  let r := generatedRefines S n
  have h := input_labels_le_qubits (state S n).presentation
    (state S n).admissible.toTannerSquareAdmissible (state_boundedValence S n)
  simp only [Triangle,Fintype.card_prod,Two,Fintype.card_fin] at h
  have hc := carrier_counts S n
  unfold frameSize
  rw [r.x_length,r.q_length,r.z_length,r.f_length,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  omega
private theorem actual_qubits_mono (S : OddScale) {i n : ℕ} (hin : i≤ n) :
    Fintype.card (state S i).presentation.Q≤ Fintype.card (state S n).presentation.Q := by
  induction n with
  | zero =>
      have hi : i=0 := by omega
      subst i
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hi : i=n+1
      · subst i; rfl
      · have hi' : i≤ n := by omega
        have hb := nextState_qubit_card_lower S n (state S n)
        change 2*Fintype.card (state S n).presentation.Q≤
          Fintype.card (state S (n+1)).presentation.Q at hb
        exact (ih hi').trans (by omega)
private theorem actual_depth_le (S : OddScale) (n : ℕ) :
    n+1≤ Fintype.card (state S n).presentation.Q := by
  have hp : n+1≤2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; nlinarith
  have hq := state_qubit_card_lower S n
  omega
private theorem inputRadius_lower (S : OddScale) (n : ℕ) :
    8≤ inputRadius S n ∧ n+2≤ inputRadius S n := by
  have hd := actual_depth_le S n
  have he := S.three_le
  unfold inputRadius
  omega
private theorem prefix_radius (S : OddScale) {i n : ℕ} (hin : i≤ n) :
    radius (generateQ S i).1 S.half≤ inputRadius S n := by
  have hf := actual_frame_size S i
  have hq := actual_qubits_mono S hin
  have hs := S.two_half_add_one
  unfold radius inputRadius
  omega
private theorem dense_lengths (F : Frame) :
    (denseXQQ F).1.length=F.nx*F.nq ∧ (denseQZQ F).1.length=F.nq*F.nz := by
  simp [denseXQQ,denseQZQ,loopQ_value,flatMapQ_value,mapQ_length,
    rangeQ_value,List.length_flatMap,List.sum_replicate,Nat.mul_comm]
private theorem vertex_length (F : Frame) :
    (vertexCodesQ F).1.length≤ F.nx+F.nq+F.nz := by
  have h := dedupQ_length_le (collectQ [loopQ F.nx (fun x => singletonQ {owner:=x}),
    loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
    loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]).1
  simpa [vertexCodesQ,collectQ,flatMapQ_value,loopQ_value,singletonQ,
    List.length_flatMap,List.sum_replicate,Nat.add_assoc] using h
private theorem edge_length (F : Frame) :
    (edgeCodesQ F).1.length≤ F.nx*F.nq+F.nq*F.nz := by
  have ha := filterQ_length (fun t : ℕ×ℕ×Bool => (t.2.2,2)) (denseXQQ F).1
  have hb := filterQ_length (fun t : ℕ×ℕ×Bool => (t.2.2,2)) (denseQZQ F).1
  have hd := dedupQ_length_le (collectQ [
    mapQ (fun t : ℕ×ℕ×Bool => emitQ {owner:=t.1,p:=t.2.1})
      (filterQ (fun t => (t.2.2,2)) (denseXQQ F).1).1,
    mapQ (fun t : ℕ×ℕ×Bool => emitQ {family:=1,owner:=t.1,p:=t.2.1})
      (filterQ (fun t => (t.2.2,2)) (denseQZQ F).1).1]).1
  rw [(dense_lengths F).1] at ha
  rw [(dense_lengths F).2] at hb
  simp only [edgeCodesQ,collectQ,flatMapQ_value,List.flatMap_cons,List.flatMap_nil,
    List.length_append,List.length_map,mapQ_length,id_eq,List.length_nil] at hd ⊢
  omega
private theorem range_power_bound (R : ℕ) (hR : 2≤ R) (a : ℕ) (ha : 1≤ a)
    (n : ℕ) (hn : n≤ R^a) : work (rangeQ n)≤ R^(7*a) := by
  have hbase : 2≤ R^a := by
    have hp := pow_mono R (by omega) ha
    have hp' : R ≤ R^a := by simpa only [pow_one] using hp
    exact hR.trans hp'
  have h := range_pow (R^a) hbase n hn
  simpa only [←pow_mul,Nat.mul_comm] using h
private theorem final_tables_work (F : Frame) :
    work (denseXQQ F)≤(radius F 0)^21 ∧
    work (denseQZQ F)≤(radius F 0)^21 ∧
    work (vertexCodesQ F)≤(radius F 0)^54 ∧
    work (edgeCodesQ F)≤(radius F 0)^80 ∧
    work (cellularBoundary1Q (vertexCodesQ F).1 (edgeCodesQ F).1)≤(radius F 0)^25 ∧
    work (cellularBoundary2Q F (edgeCodesQ F).1)≤(radius F 0)^25 ∧
    work (triangleCodesQ F)≤(radius F 0)^54 := by
  let R := radius F 0
  have hR : 2≤ R := radius_two F 0
  have hco := radius_components F 0
  have nx : F.nx≤ R := by omega
  have nq : F.nq≤ R := by omega
  have nz : F.nz≤ R := by omega
  have nf : F.nf≤ R := by omega
  have nl : F.faces.length≤ R := by omega
  have incost (b : ℕ) : 9*F.faces.length+4≤ R^6 := by
    have hp := pow_constant R 1 5 32 hR (by decide)
    simp only [pow_one] at hp
    change 32*R≤R^6 at hp

    omega
  have hdenseX : work (denseXQQ F)≤ R^21 := loop_pow R hR 11 F.nx nx _ (by
    intro x hx
    have ho := map_pow R hR 1 6 (fun q => let h := xqQ F x q; ((x,q,h.1),h.2+4))
      (rangeQ F.nq).1 (by simpa [rangeQ_value] using nq) (by intro q hq; simpa only [xqQ_cost] using incost q)
    exact attach_pow R hR 10 _ _ ho ((work_cost _).trans
      (relax R hR (by omega) (range_pow R hR F.nq nq))))
  have hdenseZ : work (denseQZQ F)≤ R^21 := loop_pow R hR 11 F.nq nq _ (by
    intro q hq
    have ho := map_pow R hR 1 6 (fun z => let h := qzQ F q z; ((q,z,h.1),h.2+4))
      (rangeQ F.nz).1 (by simpa [rangeQ_value] using nz) (by intro z hz; simpa only [qzQ_cost] using incost z)
    exact attach_pow R hR 10 _ _ ho ((work_cost _).trans
      (relax R hR (by omega) (range_pow R hR F.nz nz))))
  have hv : work (vertexCodesQ F)≤ R^54 := by
    let raw := collectQ [loopQ F.nx (fun x => singletonQ {owner:=x}),
      loopQ F.nq (fun q => singletonQ {family:=1,owner:=q}),
      loopQ F.nz (fun z => singletonQ {family:=2,owner:=z})]
    have hr : work raw≤ R^21 := collect_pow R hR 2 16 _
      (by exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2)) (by
        intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        · exact loop_pow R hR 6 F.nx nx _ (by intros; exact singleton_pow R hR _)
        · exact loop_pow R hR 6 F.nq nq _ (by intros; exact singleton_pow R hR _)
        · exact loop_pow R hR 6 F.nz nz _ (by intros; exact singleton_pow R hR _))
    have hu := dedup_pow R hR 21 raw.1 ((work_length _).trans hr)
    have hh : raw.2+1≤ R^52 := by
      have hp := pow_mono R (by omega) (by decide : 21≤51)
      have hs := pow_sum R 51 hR ((work_cost _).trans (hr.trans hp)) (pow_one_le R 51 (by omega))
      exact hs
    have h : work ((dedupQ raw.1).1,(raw.2+1)+(dedupQ raw.1).2) ≤ R^53 :=
      attach_pow R hR 52 (dedupQ raw.1) (raw.2+1) hu hh
    have hfinal : work (vertexCodesQ F) ≤ R^53 := by
      refine (work_mono_value_cost (vertexCodesQ F) _ (by rfl) ?_).trans h
      change raw.2+(dedupQ raw.1).2+1 ≤ (raw.2+1)+(dedupQ raw.1).2
      omega
    exact relax R hR (by decide : 53≤54) hfinal
  have he : work (edgeCodesQ F)≤ R^80 := by
    let ax := filterQ (fun t : ℕ×ℕ×Bool => (t.2.2,2)) (denseXQQ F).1
    let bz := filterQ (fun t : ℕ×ℕ×Bool => (t.2.2,2)) (denseQZQ F).1
    have ha : work ax≤ R^25 := filter_pow R hR 21 1 _ _ ((work_length _).trans hdenseX)
      (by intros; simpa using hR)
    have hb : work bz≤ R^25 := filter_pow R hR 21 1 _ _ ((work_length _).trans hdenseZ)
      (by intros; simpa using hR)
    let left := mapQ (fun t : ℕ×ℕ×Bool => emitQ {owner:=t.1,p:=t.2.1}) ax.1
    let right := mapQ (fun t : ℕ×ℕ×Bool => emitQ {family:=1,owner:=t.1,p:=t.2.1}) bz.1
    have hl : work left≤ R^29 := map_pow R hR 21 5 _ _
      ((filterQ_length _ _).trans ((work_length _).trans hdenseX)) (by intros; exact Nat.pow_le_pow_left hR 5)
    have hr : work right≤ R^29 := map_pow R hR 21 5 _ _
      ((filterQ_length _ _).trans ((work_length _).trans hdenseZ)) (by intros; exact Nat.pow_le_pow_left hR 5)
    let out := collectQ [left,right]
    have ho : work out≤ R^33 := collect_pow R hR 1 29 _ (by simpa using hR) (by
      intro q hq; simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl <;> assumption)
    have hu := dedup_pow R hR 33 out.1 ((work_length _).trans ho)
    have hh : (denseXQQ F).2+(denseQZQ F).2+ax.2+bz.2+out.2+1≤2^3*R^76 := by
      have h21 := pow_mono R (by omega) (by decide : 21≤76)
      have h25 := pow_mono R (by omega) (by decide : 25≤76)
      have h33 := pow_mono R (by omega) (by decide : 33≤76)
      have h1 := pow_one_le R 76 (by omega)
      have a := (work_cost _).trans hdenseX
      have b := (work_cost _).trans hdenseZ
      have c := (work_cost _).trans ha
      have d := (work_cost _).trans hb
      have e := (work_cost _).trans ho
      omega
    have h : work ((dedupQ out.1).1,
        ((denseXQQ F).2+(denseQZQ F).2+ax.2+bz.2+out.2+1)+(dedupQ out.1).2) ≤ R^80 :=
      attach_fixed R hR 76 3 (dedupQ out.1) _ hu hh
    refine (work_mono_value_cost (edgeCodesQ F) _ (by rfl) ?_).trans h
    change (denseXQQ F).2+(denseQZQ F).2+ax.2+bz.2+out.2+(dedupQ out.1).2+1 ≤ ((denseXQQ F).2+(denseQZQ F).2+ax.2+bz.2+out.2+1)+(dedupQ out.1).2
    omega
  have lv : (vertexCodesQ F).1.length≤ R^3 := by
    have hl := vertex_length F
    have hp := pow_constant R 1 2 4 hR (by decide)
    simp only [pow_one] at hp
    change 4*R≤R^3 at hp

    omega
  have le : (edgeCodesQ F).1.length≤ R^3 := by
    have hl := edge_length F
    have hp := pow_constant R 2 1 2 hR (by decide)
    change 2*R^2≤R^3 at hp
    nlinarith
  have hm1 : work (cellularBoundary1Q (vertexCodesQ F).1 (edgeCodesQ F).1)≤ R^25 := by
    have hlv := range_power_bound R hR 3 (by decide) _ lv
    have hle := range_power_bound R hR 3 (by decide) _ le
    have ho : work (flatMapQ (fun e => mapQ (fun v =>
        let ec := (edgeCodesQ F).1[e]?.getD {}
        let vc := (vertexCodesQ F).1[v]?.getD {}
        let hit := edgeVertexTestQ ec vc
        ((v,e,hit.1),2*e+2*v+hit.2+8)) (rangeQ (vertexCodesQ F).1.length).1)
        (rangeQ (edgeCodesQ F).1.length).1)≤ R^20 :=
      flat_pow R hR 3 14 _ _ (by simpa [rangeQ_value] using le) (by
        intro e hem
        have hem' : e<(edgeCodesQ F).1.length := by simpa [rangeQ_value] using hem
        exact map_pow R hR 3 8 _ _ (by simpa [rangeQ_value] using lv) (by
          intro v hvm
          have hvm' : v<(vertexCodesQ F).1.length := by simpa [rangeQ_value] using hvm
          have hp := pow_constant R 3 5 32 hR (by decide)
          change 32*R^3≤R^8 at hp
          have h1 := pow_one_le R 3 (by omega)
          simp only [edgeVertexTestQ]; omega))
    have hh : (vertexCodesQ F).1.length+(edgeCodesQ F).1.length+
        (rangeQ (edgeCodesQ F).1.length).2+(rangeQ (vertexCodesQ F).1.length).2+2≤2^3*R^21 := by
      have h3 := pow_mono R (by omega) (by decide : 3≤21)
      have p9 : R^(7*3)≤R^21 := by
        simpa only [show (7*3:ℕ)=21 from rfl] using Nat.le_refl (R^21)
      have a := (work_cost _).trans (hlv.trans p9)
      have b := (work_cost _).trans (hle.trans p9)
      have h1 := pow_one_le R 21 (by omega)
      omega
    have h := attach_fixed R hR 21 3 _ _ (relax R hR (by omega) ho) hh
    refine (work_mono_value_cost (cellularBoundary1Q (vertexCodesQ F).1 (edgeCodesQ F).1) _ (by rfl) ?_).trans h
    change (vertexCodesQ F).1.length+(edgeCodesQ F).1.length+
      (rangeQ (edgeCodesQ F).1.length).2+(rangeQ (vertexCodesQ F).1.length).2+
      (flatMapQ (fun e => mapQ (fun v =>
        let ec := (edgeCodesQ F).1[e]?.getD {}
        let vc := (vertexCodesQ F).1[v]?.getD {}
        let hit := edgeVertexTestQ ec vc
        ((v,e,hit.1),2*e+2*v+hit.2+8))
        (rangeQ (vertexCodesQ F).1.length).1) (rangeQ (edgeCodesQ F).1.length).1).2+2 ≤
      ((vertexCodesQ F).1.length+(edgeCodesQ F).1.length+
        (rangeQ (edgeCodesQ F).1.length).2+(rangeQ (vertexCodesQ F).1.length).2+2)+
      (flatMapQ (fun e => mapQ (fun v =>
        let ec := (edgeCodesQ F).1[e]?.getD {}
        let vc := (vertexCodesQ F).1[v]?.getD {}
        let hit := edgeVertexTestQ ec vc
        ((v,e,hit.1),2*e+2*v+hit.2+8))
        (rangeQ (vertexCodesQ F).1.length).1) (rangeQ (edgeCodesQ F).1.length).1).2
    omega
  have hm2 : work (cellularBoundary2Q F (edgeCodesQ F).1)≤ R^25 := by
    have hrf := range_pow R hR F.nf nf
    have hre := range_power_bound R hR 3 (by decide) _ le
    have ho : work (flatMapQ (fun f =>
        let row := faceAtQ F.faces f
        let cells := mapQ (fun e =>
          let ec := (edgeCodesQ F).1[e]?.getD {}
          let hit := faceEdgeTestQ row.1 ec
          ((e,f,hit.1),2*e+hit.2+6)) (rangeQ (edgeCodesQ F).1.length).1
        (cells.1,row.2+cells.2)) (rangeQ F.nf).1)≤ R^18 :=
      flat_pow R hR 1 14 _ _ (by simpa [rangeQ_value] using nf) (by
        intro f hfm
        have hr : (faceAtQ F.faces f).2≤ R^13 := by
          have h := faceAtQ_cost_le F.faces f
          have hp := pow_constant R 1 12 4096 hR (by decide)
          simp only [pow_one] at hp
          change 4096*R≤R^13 at hp

          omega
        have hc : work (mapQ (fun e =>
            let ec := (edgeCodesQ F).1[e]?.getD {}
            let hit := faceEdgeTestQ (faceAtQ F.faces f).1 ec
            ((e,f,hit.1),2*e+hit.2+6)) (rangeQ (edgeCodesQ F).1.length).1)≤ R^13 :=
          map_pow R hR 3 7 _ _ (by simpa [rangeQ_value] using le) (by
            intro e hem
            have hem' : e<(edgeCodesQ F).1.length := by simpa [rangeQ_value] using hem
            have hp := pow_constant R 3 4 16 hR (by decide)
            have hrange : e < R^3 := lt_of_lt_of_le hem' le
            have h2 : 2≤ R^3 := (show 2≤2^3 by decide).trans (Nat.pow_le_pow_left hR 3)
            change 2*e+20+6 ≤ R^7
            change 16*R^3 ≤ R^7 at hp
            omega)
        exact attach_pow R hR 13 _ _ hc hr)
    have hh : (edgeCodesQ F).1.length+(rangeQ F.nf).2+
        (rangeQ (edgeCodesQ F).1.length).2+2≤2^3*R^21 := by
      have h3 := pow_mono R (by omega) (by decide : 3≤21)
      have p9 : R^(7*3)≤R^21 := by
        simpa only [show (7*3:ℕ)=21 from rfl] using Nat.le_refl (R^21)
      have p7 := pow_mono R (by omega) (by decide : 7≤21)
      have a := (work_cost _).trans (hrf.trans p7)
      have b := (work_cost _).trans (hre.trans p9)
      have h7 := pow_mono R (by omega) (by decide : 7≤21)
      have h1 := pow_one_le R 21 (by omega)
      omega
    have h := attach_fixed R hR 21 3 _ _ (relax R hR (by omega) ho) hh
    refine (work_mono_value_cost (cellularBoundary2Q F (edgeCodesQ F).1) _ (by rfl) ?_).trans h
    change (edgeCodesQ F).1.length+(rangeQ F.nf).2+
      (rangeQ (edgeCodesQ F).1.length).2+
      (flatMapQ (fun f =>
        let row := faceAtQ F.faces f
        let cells := mapQ (fun e =>
          let ec := (edgeCodesQ F).1[e]?.getD {}
          let hit := faceEdgeTestQ row.1 ec
          ((e,f,hit.1),2*e+hit.2+6)) (rangeQ (edgeCodesQ F).1.length).1
        (cells.1,row.2+cells.2)) (rangeQ F.nf).1).2+2 ≤
      ((edgeCodesQ F).1.length+(rangeQ F.nf).2+(rangeQ (edgeCodesQ F).1.length).2+2)+
      (flatMapQ (fun f =>
        let row := faceAtQ F.faces f
        let cells := mapQ (fun e =>
          let ec := (edgeCodesQ F).1[e]?.getD {}
          let hit := faceEdgeTestQ row.1 ec
          ((e,f,hit.1),2*e+hit.2+6)) (rangeQ (edgeCodesQ F).1.length).1
        (cells.1,row.2+cells.2)) (rangeQ F.nf).1).2
    omega
  have htri : work (triangleCodesQ F)≤ R^54 := by
    let raw := loopQ F.nf (fun f => mapQ (fun d => emitQ {family:=3,owner:=f,copy:=d}) [0,1])
    have hr : work raw≤ R^19 := loop_pow R hR 9 F.nf nf _ (by
      intros; exact map_pow R hR 1 5 _ _ (by simpa using hR) (by intros; exact Nat.pow_le_pow_left hR 5))
    have hu := dedup_pow R hR 19 raw.1 ((work_length _).trans hr)
    have h : work ((dedupQ raw.1).1,raw.2+(dedupQ raw.1).2) ≤ R^49 :=
      attach_pow R hR 48 (dedupQ raw.1) raw.2 hu
      ((work_cost _).trans (relax R hR (by omega) hr))
    have hfinal : work (triangleCodesQ F) ≤ R^49 := by
      refine (work_mono_value_cost (triangleCodesQ F) _ (by rfl) ?_).trans h
      change raw.2+(dedupQ raw.1).2 ≤ raw.2+(dedupQ raw.1).2
      exact Nat.le_refl _
    exact relax R hR (by decide : 49≤54) hfinal
  exact ⟨hdenseX,hdenseZ,hv,he,hm1,hm2,htri⟩
namespace Allocation
end Allocation
attribute [local simp] allocation_appendQ_value
attribute [local simp] allocation_equalCodeQ_value
attribute [local simp] allocation_xqFaceTestQ_value
attribute [local simp] allocation_qzFaceTestQ_value
attribute [local simp] allocation_xqQ_value
attribute [local simp] allocation_qzQ_value
attribute [local simp] allocation_seedFrameQ_value
attribute [local simp] allocation_emitQ_value
attribute [local simp] allocation_singletonQ_value
attribute [local simp] allocation_mapCodesQ_value
attribute [local simp] allocation_facesAtXQ_value
attribute [local simp] allocation_starQsQ_value
attribute [local simp] allocation_starZsQ_value
attribute [local simp] allocation_starSidesQ_value
attribute [local simp] allocation_subVerticesQ_value
attribute [local simp] allocation_subEdgesQ_value
attribute [local simp] allocation_subFacesQ_value
attribute [local simp] allocation_doubleVerticesQ_value
attribute [local simp] allocation_doubleEdgesQ_value
attribute [local simp] allocation_doubleFacesQ_value
attribute [local simp] allocation_qNeighborsQ_value
attribute [local simp] allocation_qDoubleVerticesQ_value
attribute [local simp] allocation_qDoubleEdgesQ_value
attribute [local simp] allocation_rxXCodesQ_value
attribute [local simp] allocation_rxQCodesQ_value
attribute [local simp] allocation_rxZCodesQ_value
attribute [local simp] allocation_gridVertexQ_value
attribute [local simp] allocation_horizontalEdgeQ_value
attribute [local simp] allocation_verticalEdgeQ_value
attribute [local simp] allocation_segmentVertexQ_value
attribute [local simp] allocation_doubleEdgeVertexQ_value
attribute [local simp] allocation_qDoubleEdgeVertexQ_value
attribute [local simp] allocation_qEdgeImageQ_value
attribute [local simp] allocation_bridgeOfVertexQ_value
attribute [local simp] allocation_rxLocalFaceCodesQ_value
attribute [local simp] allocation_rxGlueFaceCodesQ_value
attribute [local simp] allocation_rxOldFaceCodesQ_value
attribute [local simp] allocation_rxFaceCodesQ_value
attribute [local simp] allocation_localFaceEndpointsQ_value
attribute [local simp] allocation_glueFaceEndpointsQ_value
attribute [local simp] allocation_oldFaceEndpointsQ_value
attribute [local simp] allocation_faceEndpointsQ_value
attribute [local simp] allocation_indexFaceQ_value
attribute [local simp] allocation_packFrameQ_value
attribute [local simp] allocation_memCodeQ_value
attribute [local simp] allocation_dedupQ_value
attribute [local simp] allocation_rxFrameQ_value
attribute [local simp] allocation_transposeFrameQ_value
attribute [local simp] allocation_rzFrameQ_value
attribute [local simp] allocation_nextFrameQ_value
attribute [local simp] allocation_historyQ_value
attribute [local simp] allocation_generateQ_value
attribute [local simp] allocation_denseXQQ_value
attribute [local simp] allocation_denseQZQ_value
attribute [local simp] allocation_vertexCodesQ_value
attribute [local simp] allocation_edgeCodesQ_value
attribute [local simp] allocation_edgeVertexTestQ_value
attribute [local simp] allocation_faceEdgeTestQ_value
attribute [local simp] allocation_cellularBoundary1Q_value
attribute [local simp] allocation_cellularBoundary2Q_value
attribute [local simp] allocation_runQ_value
attribute [local simp] allocation_seedRowsQ_value
attribute [local simp] allocation_triangleCodesQ_value
attribute [local simp] allocation_setupQ_value
end QEC.Coding.BDL26NativePresentationGenerator
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (setupQ S n).2≤(n+1)*(inputRadius S n)^setupExponent := by
  let R := inputRadius S n
  let F := (generateQ S n).1
  have hR := (inputRadius_lower S n).1
  have hf := prefix_radius S (show n≤ n from le_rfl)
  have hf0 : radius F 0≤ R := by
    change radius F S.half ≤ R at hf
    unfold radius at hf ⊢
    omega
  have ht := final_tables_work F
  have hgen : (generateQ S n).2 ≤ (n+1)*R^205 := generate_cost S n
  have hseed : seedRowsQ.2≤ R^205 := by
    have hs : seedRowsQ.2=151 := by decide
    have hp := Nat.pow_le_pow_left (show 2≤ R by omega) 8
    have hm := pow_mono R (by omega) (by decide : 8≤205)
    omega
  have hs21 := Nat.pow_le_pow_left hf0 21
  have hs54 := Nat.pow_le_pow_left hf0 54
  have hs80 := Nat.pow_le_pow_left hf0 80
  have hs25 := Nat.pow_le_pow_left hf0 25
  have hs19 := Nat.pow_le_pow_left hf0 54
  have a := (work_cost _).trans ht.1
  have b := (work_cost _).trans ht.2.1
  have c := (work_cost _).trans ht.2.2.1
  have d := (work_cost _).trans ht.2.2.2.1
  have e := (work_cost _).trans ht.2.2.2.2.1
  have f := (work_cost _).trans ht.2.2.2.2.2.1
  have g := (work_cost _).trans ht.2.2.2.2.2.2
  have p21 := pow_mono R (by omega) (by decide : 21≤205)
  have p54 := pow_mono R (by omega) (by decide : 54≤205)
  have p80 := pow_mono R (by omega) (by decide : 80≤205)
  have p25 := pow_mono R (by omega) (by decide : 25≤205)
  have p19 := pow_mono R (by omega) (by decide : 54≤205)
  have h1 := pow_one_le R 205 (by omega)
  have hp := pow_constant R 205 15 32768 (by omega) (by decide)
  change 32768*R^205≤R^220 at hp
  have a205 := (a.trans hs21).trans p21
  have b205 := (b.trans hs21).trans p21
  have c205 := (c.trans hs54).trans p54
  have d205 := (d.trans hs80).trans p80
  have e205 := (e.trans hs25).trans p25
  have f205 := (f.trans hs25).trans p25
  have g205 := (g.trans hs19).trans p19
  have hother : (denseXQQ F).2+(denseQZQ F).2+
      (vertexCodesQ F).2+(edgeCodesQ F).2+
      (cellularBoundary1Q (vertexCodesQ F).1 (edgeCodesQ F).1).2+
      (cellularBoundary2Q F (edgeCodesQ F).1).2+8+
      (triangleCodesQ F).2+seedRowsQ.2+5≤32*R^205 := by omega
  have hu : R^205≤(n+1)*R^205 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (R^205) (show 1≤n+1 by omega)
  dsimp only [setupQ,runQ]
  change (generateQ S n).2+(denseXQQ F).2+(denseQZQ F).2+
    (vertexCodesQ F).2+(edgeCodesQ F).2+
    (cellularBoundary1Q (vertexCodesQ F).1 (edgeCodesQ F).1).2+
    (cellularBoundary2Q F (edgeCodesQ F).1).2+8+
    (triangleCodesQ F).2+seedRowsQ.2+5≤(n+1)*R^220
  calc
    _ ≤ (n+1)*R^205+32*R^205 := by omega
    _ ≤ 33*((n+1)*R^205) := by omega
    _ = (n+1)*(33*R^205) := Nat.mul_left_comm 33 (n+1) (R^205)
    _ ≤ (n+1)*(32768*R^205) := Nat.mul_le_mul_left (n+1)
      (Nat.mul_le_mul_right (R^205) (by decide : 33≤32768))
    _ ≤ (n+1)*R^220 := Nat.mul_le_mul_left (n+1) hp
end QEC.Coding.BDL26NativePresentationGenerator
