-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.rx_step_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:48:05.515202+00:00
-- url     : https://prove2.me/submissions/98cb39a3-b952-4122-b0b7-8a9409c57085

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_mapQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_filterQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_rangeQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_handleQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_anyQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xqQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qzQ_cost
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_faceAtQ_cost_le
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_dedupQ_length_le
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
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
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
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
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
private theorem mapQ_cost_constant {A B : Type*} (f : A → Query B) (as : List A)
    (c : ℕ) (hc : ∀a∈as,(f a).2=c) : (mapQ f as).2=(c+1)*as.length := by
  induction as with
  | nil => simp [mapQ]
  | cons a as ih =>
      have ha := hc a (by simp)
      have ht := ih (fun x hx => hc x (by simp [hx]))
      simp only [mapQ,List.length_cons,ha,ht]
      ring
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
private theorem flattenQ_cost {A : Type*} (as : List (List A)) :
    (flattenQ as).2=(as.map List.length).sum+2*as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [flattenQ,appendQ,ih,List.map_cons,List.sum_cons,List.length_cons]; ring
private theorem productQ_length {A B : Type*} (as : List A) (bs : List B) :
    (productQ as bs).1.length=as.length*bs.length := by
  simp [productQ_value,List.length_flatMap,Nat.mul_comm]
private theorem productQ_cost {A B : Type*} (as : List A) (bs : List B) :
    (productQ as bs).2=3*as.length*bs.length+3*as.length := by
  have hm (a : A) : (mapQ (fun b : B => ((a,b),1)) bs).2=2*bs.length :=
    mapQ_cost_constant _ _ 1 (by intro b hb; rfl)
  have ho := mapQ_cost_constant (fun a : A => mapQ (fun b : B => ((a,b),1)) bs)
    as (2*bs.length) (by intro a ha; exact hm a)
  simp only [productQ,ho,flattenQ_cost,mapQ_value,List.length_map]
  simp [List.map_map,mapQ_length,Function.comp_def]
  ring
private theorem radius_components (F : Frame) (m : ℕ) :
    F.nx+1≤ radius F m ∧ F.nq+1≤ radius F m ∧ F.nz+1≤ radius F m ∧
    F.nf+1≤ radius F m ∧ F.faces.length+1≤ radius F m ∧ m+1≤ radius F m := by
  simp only [radius,frameSize]
  omega
private theorem starQs_length (F : Frame) (x : ℕ) : (starQsQ F x).1.length≤ F.nq := by
  exact (filterQ_length _ _).trans_eq (by simp [rangeQ_value])
private theorem starZs_length (F : Frame) (x : ℕ) : (starZsQ F x).1.length≤ F.nz := by
  exact (filterQ_length _ _).trans_eq (by simp [rangeQ_value])
private theorem starSides_length (F : Frame) (x : ℕ) :
    (starSidesQ F x).1.length≤ F.nq*F.nz := by
  exact (filterQ_length _ _).trans_eq (by simp [rangeQ_value,productQ_length])
private theorem facesAtX_length (F : Frame) (x : ℕ) :
    (facesAtXQ F x).1.length≤ F.nf := by
  exact (filterQ_length _ _).trans_eq (by simp [rangeQ_value,mapQ_value])
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
private theorem filter_pow_succ {A : Type*} (R : ℕ) (hR : 2≤ R) (a b : ℕ)
    (f : A → Query Bool) (as : List A) (ha : as.length+1≤ R^a)
    (hf : ∀x∈as,(f x).2≤ R^b) : work (filterQ f as)≤ R^(a+b+2) := by
  have h := filterQ_work f as (R^b) hf
  have h1 := pow_one_le R b (by omega)
  calc
    work (filterQ f as) ≤ (as.length+1)*(R^b+3) := h
    _ ≤ R^a*(4*R^b) := Nat.mul_le_mul ha (by omega)
    _ = 4*R^(a+b) := by rw [pow_add]; ring
    _ ≤ R^(a+b+2) := pow_constant R (a+b) 2 4 hR (by decide)
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
private theorem codes_pow (R : ℕ) (hR : 2≤ R) (a : ℕ)
    (f : Code → Code) (as : List Code) (ha : as.length≤ R^a) :
    work (mapCodesQ f as)≤ R^(a+8) := by
  exact map_pow R hR a 5 (fun c => emitQ (f c)) as ha
    (by intro c hc; exact (show 32≤2^5 by decide).trans (Nat.pow_le_pow_left hR 5))
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
private theorem scan_bounds (F : Frame) (x m : ℕ) :
    work (starQsQ F x)≤(radius F m)^9 ∧
    work (starZsQ F x)≤(radius F m)^9 ∧
    work (starSidesQ F x)≤(radius F m)^13 ∧
    work (facesAtXQ F x)≤(radius F m)^10 ∧
    (∀q,work (qNeighborsQ F q)≤(radius F m)^9) := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hF := radius_components F m
  have hface : F.faces.length≤ R := by omega
  have nq : F.nq≤ R := by omega
  have nz : F.nz≤ R := by omega
  have nf : F.nf≤ R := by omega
  have h9 : 9*F.faces.length≤ R^5 := by
    have h := pow_constant R 1 4 16 hR (by decide)
    simp only [pow_one] at h
    change 16*R≤R^5 at h
    omega
  have h6 : 6*F.faces.length≤ R^4 := by
    have h := pow_constant R 1 3 8 hR (by decide)
    simp only [pow_one] at h
    change 8*R≤R^4 at h
    omega
  have hrq := range_pow R hR F.nq nq
  have hrz := range_pow R hR F.nz nz
  have hrf := range_pow R hR F.nf nf
  have qbound (q : ℕ) : work (qNeighborsQ F q)≤ R^9 := by
    have ho := filter_pow_succ R hR 1 5 (qzQ F q) (rangeQ F.nz).1
      (by simpa only [rangeQ_value,List.length_range,pow_one] using hF.2.2.1) (by intro z hz; rw [qzQ_cost]; exact h9)
    exact attach_pow R hR 8 _ (rangeQ F.nz).2 ho
      ((work_cost _).trans (hrz.trans (pow_mono R (by omega) (by decide))))
  refine ⟨?_,?_,?_,?_,qbound⟩
  · have ho := filter_pow_succ R hR 1 5 (xqQ F x) (rangeQ F.nq).1
      (by simpa only [rangeQ_value,List.length_range,pow_one] using hF.2.1) (by intro q hq; rw [xqQ_cost]; exact h9)
    exact attach_pow R hR 8 _ (rangeQ F.nq).2 ho
      ((work_cost _).trans (hrq.trans (pow_mono R (by omega) (by decide))))
  · have ho := filter_pow_succ R hR 1 4 (fun z => anyQ
        (fun f : FaceRow => (decide (f.x=x ∧ f.z=z),5)) F.faces) (rangeQ F.nz).1
      (by simpa only [rangeQ_value,List.length_range,pow_one] using hF.2.2.1) (by
        intro z hz
        rw [anyQ_cost _ _ 5 (by intros; rfl)]
        exact h6)
    have h := attach_pow R hR 7 _ (rangeQ F.nz).2 ho ((work_cost _).trans hrz)
    exact h.trans (pow_mono R (by omega) (by decide))
  · have hp : work (productQ (rangeQ F.nq).1 (rangeQ F.nz).1)≤ R^5 := by
      simp only [work,productQ_length,productQ_cost,rangeQ_value,List.length_range]
      have h := pow_constant R 2 3 8 hR (by decide)
      change 8*R^2≤R^5 at h
      nlinarith
    have h11 : 11*F.faces.length≤ R^5 := by
      have h := pow_constant R 1 4 16 hR (by decide)
      simp only [pow_one] at h
      change 16*R≤R^5 at h
      omega
    have ho := filter_pow R hR 2 5 (fun e : ℕ×ℕ => anyQ
        (fun f : FaceRow => (decide (f.x=x ∧ f.z=e.2 ∧ (f.q0=e.1 ∨ f.q1=e.1)),10)) F.faces)
      (productQ (rangeQ F.nq).1 (rangeQ F.nz).1).1
      (by simp only [productQ_length,rangeQ_value,List.length_range]; nlinarith)
      (by intro e he; rw [anyQ_cost _ _ 10 (by intros; rfl)]; exact h11)
    have hs : (rangeQ F.nq).2+(rangeQ F.nz).2+
        (productQ (rangeQ F.nq).1 (rangeQ F.nz).1).2≤4*R^10 := by
      have hq := (work_cost _).trans (hrq.trans (pow_mono R (by omega) (by decide : 7≤10)))
      have hz := (work_cost _).trans (hrz.trans (pow_mono R (by omega) (by decide : 7≤10)))
      have hp' := (work_cost _).trans (hp.trans (pow_mono R (by omega) (by decide : 5≤10)))
      omega
    have h := attach_fixed R hR 10 2 _ _ ho hs
    exact h
  · have hm := map_pow R hR 1 4 (fun i : ℕ =>
        ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) (rangeQ F.nf).1
      (by simpa [rangeQ_value] using nf) (by
        intro i hi
        have hi' : i< F.nf := by simpa [rangeQ_value] using hi
        have hc := pow_constant R 1 3 8 hR (by decide)
        simp only [pow_one] at hc
        change 8*R≤R^4 at hc

        have hc' := pow_mono R (by omega) (by decide : 4≤4)
        nlinarith)
    have hl : (mapQ (fun i : ℕ => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) (rangeQ F.nf).1).1.length≤ R := by
      simpa [mapQ_length,rangeQ_value] using nf
    have hf := filter_pow R hR 1 2 (fun f : ℕ×FaceRow => (decide (f.2.x=x),3)) _
      (by simpa only [pow_one] using hl)
      (by intro a ha; exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2))
    have hx := attach_fixed R hR 8 1 _ ((rangeQ F.nf).2+
      (mapQ (fun i : ℕ => ((i,F.faces[i]?.getD ⟨{},0,0,0,0⟩),2*i+3)) (rangeQ F.nf).1).2)
      (hf.trans (pow_mono R (by omega) (by decide))) (by
        have hr := (work_cost _).trans (hrf.trans (pow_mono R (by omega) (by decide : 7≤8)))
        have hm' := (work_cost _).trans (hm.trans (pow_mono R (by omega) (by decide : 8≤8)))
        omega)
    exact hx
private theorem relax {A : Type*} (R : ℕ) (hR : 2≤ R) {a b : ℕ}
    (hab : a≤ b) {q : Query (List A)} (hq : work q≤ R^a) : work q≤ R^b :=
  hq.trans (pow_mono R (by omega) hab)
private theorem attach_many {A : Type*} (R : ℕ) (hR : 2≤ R) (d k : ℕ)
    (q : Query (List A)) (cs : List ℕ) (hq : work q≤ R^d)
    (hn : cs.length≤2^k) (hc : ∀c∈cs,c≤ R^d) :
    work (q.1,cs.sum+q.2)≤ R^(d+k+1) := by
  have sum_bound : ∀as : List ℕ,(∀c∈as,c≤ R^d) → as.sum≤ as.length*R^d := by
    intro as
    induction as with
    | nil => intro ha; simp
    | cons c cs ih =>
        intro ha
        have hhead := ha c (by simp)
        have htail := ih (fun a hmem => ha a (by simp only [List.mem_cons]; exact Or.inr hmem))
        simp only [List.sum_cons,List.length_cons,Nat.add_mul]
        omega
  exact attach_fixed R hR d k q _ hq ((sum_bound cs hc).trans (Nat.mul_le_mul_right _ hn))
private theorem sub_catalogue_work (F : Frame) (x m : ℕ) :
    work (subVerticesQ F x m)≤(radius F m)^40 ∧
    work (subEdgesQ F x m)≤(radius F m)^40 ∧
    work (subFacesQ F x m)≤(radius F m)^32 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hco := radius_components F m
  have hm : m≤ R := by omega
  have hm' : m-1≤ R := by omega
  have scans := scan_bounds F x m
  have lq : (starQsQ F x).1.length≤ R^1 := by simpa using (starQs_length F x).trans (by omega)
  have lz : (starZsQ F x).1.length≤ R^1 := by simpa using (starZs_length F x).trans (by omega)
  have ls : (starSidesQ F x).1.length≤ R^2 := by
    have h := starSides_length F x
    dsimp [R] at *
    nlinarith
  have lf : (facesAtXQ F x).1.length≤ R^1 := by
    simpa using (facesAtX_length F x).trans (by omega)
  have single (c : Code) : work (singletonQ c)≤ R^6 := singleton_pow R hR c
  have grid (a b : ℕ) (ha : a≤ R) (hb : b≤ R) (f : ℕ → ℕ → Code) :
      work (loopQ a (fun i => loopQ b (fun j => singletonQ (f i j))))≤ R^26 := by
    exact loop_pow R hR 16 a ha _ (by intro i hi; exact loop_pow R hR 6 b hb _ (by intros; exact single _))
  have seg (a : ℕ) (ha : a≤ R) (f : ℕ → Code) :
      work (loopQ a (fun i => singletonQ (f i)))≤ R^16 :=
    loop_pow R hR 6 a ha _ (by intros; exact single _)
  have emitted (as : List ℕ) (ha : as.length≤ R^1) (f : ℕ → Code) :
      work (mapQ (fun a => emitQ (f a)) as)≤ R^9 :=
    map_pow R hR 1 5 _ as ha (by intros; exact (Nat.pow_le_pow_left hR 5))
  have qv := emitted (starQsQ F x).1 lq (fun q : ℕ => {owner:=x,part:=1,p:=q})
  have zv := emitted (starZsQ F x).1 lz (fun z : ℕ => {owner:=x,part:=2,p:=z})
  have radial (a : ℕ) (ha : a≤ R) (part : ℕ) :
      work (flatMapQ (fun q => loopQ a (fun i => singletonQ {owner:=x,part:=part,p:=q,i:=i}))
        (starQsQ F x).1)≤ R^20 :=
    flat_pow R hR 1 16 _ _ lq (by intro q hq; exact seg a ha _)
  have side (a : ℕ) (ha : a≤ R) (part : ℕ) :
      work (flatMapQ (fun e : ℕ×ℕ => loopQ a (fun i =>
        singletonQ {owner:=x,part:=part,p:=e.1,q:=e.2,i:=i}))
        (starSidesQ F x).1)≤ R^21 :=
    flat_pow R hR 2 16 _ _ ls (by intro e he; exact seg a ha _)
  have bulk (a b : ℕ) (ha : a≤ R) (hb : b≤ R) (part : ℕ) :
      work (flatMapQ (fun f : ℕ×FaceRow => loopQ a (fun i => loopQ b (fun j =>
        singletonQ {owner:=x,part:=part,p:=f.1,i:=i,j:=j}))) (facesAtXQ F x).1)≤ R^30 :=
    flat_pow R hR 1 26 _ _ lf (by intro f hf; exact grid a b ha hb _)
  have small6 : 6≤ R^3 := (show 6≤2^3 by decide).trans (Nat.pow_le_pow_left hR 3)
  have small4 : 4≤ R^2 := (show 4≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2)
  constructor
  · let out := collectQ [singletonQ {owner:=x},
      mapQ (fun q => emitQ {owner:=x,part:=1,p:=q}) (starQsQ F x).1,
      mapQ (fun z => emitQ {owner:=x,part:=2,p:=z}) (starZsQ F x).1,
      flatMapQ (fun q => loopQ (m-1) (fun i => singletonQ {owner:=x,part:=3,p:=q,i:=i})) (starQsQ F x).1,
      flatMapQ (fun e => loopQ (m-1) (fun i => singletonQ {owner:=x,part:=4,p:=e.1,q:=e.2,i:=i})) (starSidesQ F x).1,
      flatMapQ (fun f => loopQ (m-1) (fun i => loopQ (m-1) (fun j =>
        singletonQ {owner:=x,part:=5,p:=f.1,i:=i,j:=j}))) (facesAtXQ F x).1]
    have ho : work out≤ R^36 := by
      apply collect_pow R hR 3 30 _ (by exact small6)
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
      · exact relax R hR (by omega) (single _)
      · exact relax R hR (by omega) qv
      · exact relax R hR (by omega) zv
      · exact relax R hR (by omega) (radial (m-1) hm' 3)
      · exact relax R hR (by omega) (side (m-1) hm' 4)
      · exact bulk (m-1) (m-1) hm' hm' 5
    have h := attach_many R hR 36 2 out
      [(starQsQ F x).2,(starZsQ F x).2,(starSidesQ F x).2,(facesAtXQ F x).2] ho (by simp only [List.length_cons,List.length_nil]; omega) (by
        intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl
        · exact (work_cost _).trans (relax R hR (by omega) scans.1)
        · exact (work_cost _).trans (relax R hR (by omega) scans.2.1)
        · exact (work_cost _).trans (relax R hR (by omega) scans.2.2.1)
        · exact (work_cost _).trans (relax R hR (by omega) scans.2.2.2.1))
    have hfinal : work (subVerticesQ F x m) ≤ R^39 := by
      refine (work_mono_value_cost (subVerticesQ F x m) _ (by rfl) ?_).trans h
      change (starQsQ F x).2+(starZsQ F x).2+(starSidesQ F x).2+(facesAtXQ F x).2+out.2 ≤ [(starQsQ F x).2,(starZsQ F x).2,(starSidesQ F x).2,(facesAtXQ F x).2].sum+out.2
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
    exact relax R hR (by decide : 39≤40) hfinal
  · constructor
    · let out := collectQ [
        flatMapQ (fun q => loopQ m (fun i => singletonQ {owner:=x,p:=q,i:=i})) (starQsQ F x).1,
        flatMapQ (fun e => loopQ m (fun i => singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) (starSidesQ F x).1,
        flatMapQ (fun f => loopQ m (fun i => loopQ (m-1) (fun j => singletonQ {owner:=x,part:=2,p:=f.1,i:=i,j:=j}))) (facesAtXQ F x).1,
        flatMapQ (fun f => loopQ (m-1) (fun i => loopQ m (fun j => singletonQ {owner:=x,part:=3,p:=f.1,i:=i,j:=j}))) (facesAtXQ F x).1]
      have ho : work out≤ R^35 := by
        apply collect_pow R hR 2 30 _ (by exact small4)
        intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl
        · exact relax R hR (by omega) (radial m hm 0)
        · exact relax R hR (by omega) (side m hm 1)
        · exact bulk m (m-1) hm hm' 2
        · exact bulk (m-1) m hm' hm 3
      have h := attach_many R hR 35 2 out
        [(starQsQ F x).2,(starSidesQ F x).2,(facesAtXQ F x).2] ho (by simp only [List.length_cons,List.length_nil]; omega) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl
          · exact (work_cost _).trans (relax R hR (by omega) scans.1)
          · exact (work_cost _).trans (relax R hR (by omega) scans.2.2.1)
          · exact (work_cost _).trans (relax R hR (by omega) scans.2.2.2.1))
      have hfinal : work (subEdgesQ F x m) ≤ R^38 := by
        refine (work_mono_value_cost (subEdgesQ F x m) _ (by rfl) ?_).trans h
        change (starQsQ F x).2+(starSidesQ F x).2+(facesAtXQ F x).2+out.2 ≤ [(starQsQ F x).2,(starSidesQ F x).2,(facesAtXQ F x).2].sum+out.2
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        omega
      exact relax R hR (by decide : 38≤40) hfinal
    · have ho := bulk m m hm hm 0
      have h := attach_pow R hR 30 _ (facesAtXQ F x).2 ho
        ((work_cost _).trans (relax R hR (by omega) scans.2.2.2.1))
      have hfinal : work (subFacesQ F x m) ≤ R^31 := by
        refine (work_mono_value_cost (subFacesQ F x m) _ (by rfl) ?_).trans h
        simp only [subFacesQ, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
      exact relax R hR (by decide : 31≤32) hfinal
private theorem double_catalogue_work (F : Frame) (x m : ℕ) :
    work (doubleVerticesQ F x m)≤(radius F m)^53 ∧
    work (doubleEdgesQ F x m)≤(radius F m)^60 ∧
    work (doubleFacesQ F x m)≤(radius F m)^52 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hb := sub_catalogue_work F x m
  have hs := scan_bounds F x m
  have hm : m≤ R := by have := radius_components F m; omega
  have copies (a : ℕ) (xs : List Code) (hx : xs.length≤ R^a) :
      work (flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) xs) [0,1])≤ R^(a+12) := by
    have hc := flat_pow R hR 1 (a+8)
      (fun c => mapCodesQ (fun v => {v with copy:=c}) xs) [0,1]
      (by simpa only [List.length_cons,List.length_nil,pow_one] using hR)
      (by intro c hc; exact codes_pow R hR a _ xs hx)
    have hexp : 1+(a+8)+3=a+12 := by omega
    rw [hexp] at hc
    exact hc
  constructor
  · have ho := copies 40 _ ((work_length _).trans hb.1)
    exact attach_pow R hR 52 _ (subVerticesQ F x m).2 ho
      ((work_cost _).trans (relax R hR (by omega) hb.1))
  · constructor
    · let boundary := filterQ (fun v : Code => (decide (v.part=1 ∨ v.part=2 ∨ v.part=4),7)) (subVerticesQ F x m).1
      have he := copies 40 _ ((work_length _).trans hb.2.1)
      have hbd : work boundary≤ R^46 := filter_pow R hR 40 3 _ _
        ((work_length _).trans hb.1) (by intro c hc; exact (show 7≤2^3 by decide).trans (Nat.pow_le_pow_left hR 3))
      have hbl : boundary.1.length≤ R^40 := (filterQ_length _ _).trans ((work_length _).trans hb.1)
      have hbridge := codes_pow R hR 40
        (fun v => {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundary.1 hbl
      let ends := flatMapQ (fun c => mapCodesQ (fun e => {e with copy:=c}) (subEdgesQ F x m).1) [0,1]
      let bridge := mapCodesQ (fun v => {v with part:=if v.part=1 then 4 else if v.part=2 then 5 else 6}) boundary.1
      have ho : work (collectQ [ends,bridge])≤ R^56 := collect_pow R hR 1 52 _
        (by simpa using hR) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl
          · exact he
          · exact relax R hR (by omega) hbridge)
      have h := attach_many R hR 56 2 (collectQ [ends,bridge])
        [(subEdgesQ F x m).2,(subVerticesQ F x m).2,boundary.2] ho (by simp only [List.length_cons,List.length_nil]; omega) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl
          · exact (work_cost _).trans (relax R hR (by omega) hb.2.1)
          · exact (work_cost _).trans (relax R hR (by omega) hb.1)
          · exact (work_cost _).trans (relax R hR (by omega) hbd))
      have hfinal : work (doubleEdgesQ F x m) ≤ R^59 := by
        refine (work_mono_value_cost (doubleEdgesQ F x m) _ (by rfl) ?_).trans h
        change (subEdgesQ F x m).2+(subVerticesQ F x m).2+boundary.2+(collectQ [ends,bridge]).2 ≤ [(subEdgesQ F x m).2,(subVerticesQ F x m).2,boundary.2].sum+(collectQ [ends,bridge]).2
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        omega
      exact relax R hR (by decide : 59≤60) hfinal
    · let ends := flatMapQ (fun c => mapCodesQ (fun f => {f with copy:=c}) (subFacesQ F x m).1) [0,1]
      let rect := flatMapQ (fun e : ℕ×ℕ => loopQ m (fun i =>
        singletonQ {owner:=x,part:=1,p:=e.1,q:=e.2,i:=i})) (starSidesQ F x).1
      have he : work ends≤ R^44 := copies 32 _ ((work_length _).trans hb.2.2)
      have hr : work rect≤ R^21 := flat_pow R hR 2 16 _ _ (by
        have h := starSides_length F x
        have hc := radius_components F m
        dsimp [R]; nlinarith) (by
          intro e he
          exact loop_pow R hR 6 m hm _ (by intros; exact singleton_pow R hR _))
      have ho : work (collectQ [ends,rect])≤ R^48 := collect_pow R hR 1 44 _
        (by simpa using hR) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl
          · exact he
          · exact relax R hR (by omega) hr)
      have h := attach_many R hR 48 1 (collectQ [ends,rect])
        [(subFacesQ F x m).2,(starSidesQ F x).2] ho (by simp only [List.length_cons,List.length_nil]; omega) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl
          · exact (work_cost _).trans (relax R hR (by omega) hb.2.2)
          · exact (work_cost _).trans (relax R hR (by omega) hs.2.2.1))
      have hfinal : work (doubleFacesQ F x m) ≤ R^50 := by
        refine (work_mono_value_cost (doubleFacesQ F x m) _ (by rfl) ?_).trans h
        change (subFacesQ F x m).2+(starSidesQ F x).2+(collectQ [ends,rect]).2 ≤ [(subFacesQ F x m).2,(starSidesQ F x).2].sum+(collectQ [ends,rect]).2
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        omega
      exact relax R hR (by decide : 50≤52) hfinal
private theorem q_catalogue_work (F : Frame) (q m : ℕ) :
    work (qDoubleVerticesQ F q m)≤(radius F m)^40 ∧
    work (qDoubleEdgesQ F q m)≤(radius F m)^32 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hco := radius_components F m
  have hm : m≤ R := by omega
  have hm' : m-1≤ R := by omega
  have hn := (scan_bounds F 0 m).2.2.2.2 q
  have hl : (qNeighborsQ F q).1.length≤ R := by
    have h : (qNeighborsQ F q).1.length≤ F.nz := by
      exact (filterQ_length _ _).trans_eq (by simp only [rangeQ_value,List.length_range])
    omega
  have endpoint : work (mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) (qNeighborsQ F q).1)≤ R^9 :=
    map_pow R hR 1 5 _ _ (by simpa using hl)
      (by intros; exact Nat.pow_le_pow_left hR 5)
  have interior : work (flatMapQ (fun z => loopQ (m-1) (fun i =>
      singletonQ {owner:=q,part:=2,p:=z,i:=i})) (qNeighborsQ F q).1)≤ R^20 :=
    flat_pow R hR 1 16 _ _ (by simpa using hl) (by
      intro z hz; exact loop_pow R hR 6 (m-1) hm' _ (by intros; exact singleton_pow R hR _))
  constructor
  · let cells := collectQ [singletonQ {owner:=q},
      mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) (qNeighborsQ F q).1,
      flatMapQ (fun z => loopQ (m-1) (fun i => singletonQ {owner:=q,part:=2,p:=z,i:=i})) (qNeighborsQ F q).1]
    have hc : work cells≤ R^25 := collect_pow R hR 2 20 _
      (by exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2)) (by
        intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl
        · exact relax R hR (by omega) (singleton_pow R hR _)
        · exact relax R hR (by omega) endpoint
        · exact interior)
    have ho : work (flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1])≤ R^37 :=
      flat_pow R hR 1 33 _ _ (by simpa using hR) (by
        intros; exact codes_pow R hR 25 _ _ ((work_length _).trans hc))
    have h := attach_many R hR 37 1 _ [(qNeighborsQ F q).2,cells.2] ho (by change 2≤2^1; exact Nat.le_refl _) (by
      intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl
      · exact (work_cost _).trans (relax R hR (by omega) hn)
      · exact (work_cost _).trans (relax R hR (by omega) hc))
    have hfinal : work (qDoubleVerticesQ F q m) ≤ R^39 := by
      refine (work_mono_value_cost (qDoubleVerticesQ F q m) _ (by rfl) ?_).trans h
      change (qNeighborsQ F q).2+cells.2+(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]).2 ≤ [(qNeighborsQ F q).2,cells.2].sum+(flatMapQ (fun c => mapCodesQ (fun v => {v with copy:=c}) cells.1) [0,1]).2
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
    exact relax R hR (by decide : 39≤40) hfinal
  · let ends := flatMapQ (fun c => flatMapQ (fun z => loopQ m (fun i =>
      singletonQ {owner:=q,copy:=c,p:=z,i:=i})) (qNeighborsQ F q).1) [0,1]
    let vertical := mapQ (fun z => emitQ {owner:=q,part:=1,p:=z}) (qNeighborsQ F q).1
    have he : work ends≤ R^24 := flat_pow R hR 1 20 _ _ (by simpa using hR) (by
      intro c hc; exact flat_pow R hR 1 16 _ _ (by simpa using hl) (by
        intro z hz; exact loop_pow R hR 6 m hm _ (by intros; exact singleton_pow R hR _)))
    have ho : work (collectQ [ends,vertical])≤ R^28 := collect_pow R hR 1 24 _
      (by simpa using hR) (by
        intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl
        · exact he
        · exact relax R hR (by omega) endpoint)
    have h := attach_pow R hR 28 _ (qNeighborsQ F q).2 ho
      ((work_cost _).trans (relax R hR (by omega) hn))
    have hfinal : work (qDoubleEdgesQ F q m) ≤ R^29 := by
      refine (work_mono_value_cost (qDoubleEdgesQ F q m) _ (by rfl) ?_).trans h
      change (qNeighborsQ F q).2+(collectQ [ends,vertical]).2 ≤ (qNeighborsQ F q).2+(collectQ [ends,vertical]).2
      exact Nat.le_refl _
    exact relax R hR (by decide : 29≤32) hfinal
private theorem rx_carrier_work (F : Frame) (m : ℕ) :
    work (rxXCodesQ F m)≤(radius F m)^63 ∧
    work (rxQCodesQ F m)≤(radius F m)^75 ∧
    work (rxZCodesQ F m)≤(radius F m)^68 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hco := radius_components F m
  have nx : F.nx≤ R := by omega
  have nq : F.nq≤ R := by omega
  have nz : F.nz≤ R := by omega
  constructor
  · exact loop_pow R hR 53 F.nx nx _ (by intro x hx; exact (double_catalogue_work F x m).1)
  · constructor
    · let qlocal := loopQ F.nq (fun q =>
        let cells := qDoubleVerticesQ F q m
        let out := mapCodesQ (fun c => {c with family:=1}) cells.1
        (out.1,cells.2+out.2))
      have hlocal : work (loopQ F.nx (fun x => doubleEdgesQ F x m))≤ R^70 :=
        loop_pow R hR 60 F.nx nx _ (by intro x hx; exact (double_catalogue_work F x m).2.1)
      have hq : work qlocal≤ R^59 := loop_pow R hR 49 F.nq nq _ (by
        intro q hq
        have h := (q_catalogue_work F q m).1
        exact attach_pow R hR 48 _ _ (codes_pow R hR 40 _ _ ((work_length _).trans h))
          ((work_cost _).trans (relax R hR (by omega) h)))
      have ho : work (collectQ [loopQ F.nx (fun x => doubleEdgesQ F x m),qlocal])≤ R^74 :=
        collect_pow R hR 1 70 _ (by simpa using hR) (by
          intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl
          · exact hlocal
          · exact relax R hR (by omega) hq)
      exact relax R hR (by omega) ho
    · let qlocal := loopQ F.nq (fun q =>
        let cells := qDoubleEdgesQ F q m
        let out := mapCodesQ (fun c => {c with family:=1}) cells.1
        (out.1,cells.2+out.2))
      let old := loopQ F.nz (fun z => mapQ (fun c => emitQ {family:=2,owner:=z,copy:=c}) [0,1])
      have hlocal : work (loopQ F.nx (fun x => doubleFacesQ F x m))≤ R^62 :=
        loop_pow R hR 52 F.nx nx _ (by intro x hx; exact (double_catalogue_work F x m).2.2)
      have hq : work qlocal≤ R^51 := loop_pow R hR 41 F.nq nq _ (by
        intro q hq
        have h := (q_catalogue_work F q m).2
        exact attach_pow R hR 40 _ _ (codes_pow R hR 32 _ _ ((work_length _).trans h))
          ((work_cost _).trans (relax R hR (by omega) h)))
      have hold : work old≤ R^19 := loop_pow R hR 9 F.nz nz _ (by
        intro z hz
        exact map_pow R hR 1 5 _ _ (by simpa using hR) (by intros; exact Nat.pow_le_pow_left hR 5))
      have ho : work (collectQ [loopQ F.nx (fun x => doubleFacesQ F x m),qlocal,old])≤ R^67 :=
        collect_pow R hR 2 62 _
          (by exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2)) (by
            intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
            rcases ha with rfl|rfl|rfl
            · exact hlocal
            · exact relax R hR (by omega) hq
            · exact relax R hR (by omega) hold)
      exact relax R hR (by omega) ho
private theorem rx_faces_work (F : Frame) (m : ℕ) :
    work (rxFaceCodesQ F m)≤(radius F m)^84 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hco := radius_components F m
  have nx : F.nx≤ R := by omega
  have nf : F.nf≤ R := by omega
  have onecopy (f : ℕ → Code) : work (mapQ (fun d => emitQ (f d)) [0,1])≤ R^9 :=
    map_pow R hR 1 5 _ _ (by simpa using hR) (by intros; exact Nat.pow_le_pow_left hR 5)
  have hlocal : work (rxLocalFaceCodesQ F m)≤ R^79 := loop_pow R hR 69 F.nx nx _ (by
    intro x hx
    have hf := (double_catalogue_work F x m).2.2
    have ho : work (flatMapQ (fun f : Code => flatMapQ (fun a =>
        mapQ (fun b => emitQ {f with k:=a,l:=b}) [0,1]) [0,1]) (doubleFacesQ F x m).1)≤ R^68 :=
      flat_pow R hR 52 13 _ _ ((work_length _).trans hf) (by
        intro f hfm
        exact flat_pow R hR 1 9 _ _ (by simpa using hR) (by intros; exact onecopy _))
    exact attach_pow R hR 68 _ _ ho ((work_cost _).trans (relax R hR (by omega) hf)))
  have hglue : work (rxGlueFaceCodesQ F m)≤ R^60 := loop_pow R hR 50 F.nx nx _ (by
    intro x hx
    have hqs := (scan_bounds F x m).1
    have lqs : (starQsQ F x).1.length≤ R := by
      have := starQs_length F x; have := radius_components F m; omega
    have hout : work (flatMapQ (fun q =>
        let es := qDoubleEdgesQ F q m
        let out := flatMapQ (fun e : Code => mapQ (fun a =>
          emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1]) es.1
        (out.1,es.2+out.2)) (starQsQ F x).1)≤ R^49 :=
      flat_pow R hR 1 45 _ _ (by simpa using lqs) (by
        intro q hq
        have he := (q_catalogue_work F q m).2
        have ho : work (flatMapQ (fun e : Code => mapQ (fun a =>
            emitQ {family:=1,owner:=x,copy:=e.copy,part:=e.part,p:=q,q:=e.p,i:=e.i,k:=a}) [0,1])
            (qDoubleEdgesQ F q m).1)≤ R^44 :=
          flat_pow R hR 32 9 _ _ ((work_length _).trans he) (by intros; exact onecopy _)
        exact attach_pow R hR 44 _ _ ho ((work_cost _).trans (relax R hR (by omega) he)))
    exact attach_pow R hR 49 _ _ hout ((work_cost _).trans (relax R hR (by omega) hqs)))
  have hold : work (rxOldFaceCodesQ F)≤ R^19 := loop_pow R hR 9 F.nf nf _ (by intros; exact onecopy _)
  exact collect_pow R hR 2 79 _
    (by exact (show 3≤2^2 by decide).trans (Nat.pow_le_pow_left hR 2)) (by
      intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      · exact hlocal
      · exact relax R hR (by omega) hglue
      · exact relax R hR (by omega) hold)
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
private theorem endpoint_cost (F : Frame) (m : ℕ) (c : Code) :
    (faceEndpointsQ F m c).2≤(radius F m)^13 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hco := radius_components F m
  have hread (i : ℕ) : (faceAtQ F.faces i).2≤ R^3 := by
    have hc := faceAtQ_cost_le F.faces i
    have hp := pow_constant R 1 2 4 hR (by decide)
    simp only [pow_one] at hp
    change 4*R≤R^3 at hp

    omega
  have h3 : 8≤ R^3 := (show 8≤2^3 by decide).trans (Nat.pow_le_pow_left hR 3)
  have h128 : 128≤ R^8 := (show 128≤2^8 by decide).trans (Nat.pow_le_pow_left hR 8)
  have hgrid (x f i j : ℕ) : (gridVertexQ F x m f i j).2≤ R^8 := by
    have hr := hread f
    have hp := pow_constant R 3 5 32 hR (by decide)
    change 32*R^3≤R^8 at hp
    have h1 := pow_one_le R 3 (by omega)
    change (faceAtQ F.faces f).2+64 ≤ R^8
    omega
  have hedge (x f i j : ℕ) : (horizontalEdgeQ F x m f i j).2≤ R^8 ∧
      (verticalEdgeQ F x m f i j).2≤ R^8 := by
    have hr := hread f
    have hp := pow_constant R 3 5 32 hR (by decide)
    change 32*R^3≤R^8 at hp
    have h1 := pow_one_le R 3 (by omega)
    constructor <;> change (faceAtQ F.faces f).2+48 ≤ R^8 <;> omega
  have hd (e : Code) (d : ℕ) : (doubleEdgeVertexQ F m e d).2≤R^9 := by
    have hp : 2*R^8 ≤ R^9 := pow_constant R 8 1 2 hR (by decide)
    have h64 : 64≤R^8 := (show 64≤2^8 by decide).trans (Nat.pow_le_pow_left hR 8)
    have hg := hgrid e.owner e.p (e.i+d) (e.j+1)
    have hg' := hgrid e.owner e.p (e.i+1) (e.j+d)
    by_cases hb : e.part≥4
    · simp only [doubleEdgeVertexQ,if_pos hb]
      exact h64.trans (pow_mono R (by omega) (by decide : 8≤9))
    · by_cases hs : e.part=0 ∨ e.part=1
      · simp only [doubleEdgeVertexQ,if_neg hb,if_pos hs]
        change 64+40 ≤ R^9
        omega
      · by_cases he : e.part=2
        · simp only [doubleEdgeVertexQ,if_neg hb,if_neg hs,if_pos he]
          change (gridVertexQ F e.owner m e.p (e.i+d) (e.j+1)).2+40 ≤ R^9
          omega
        · simp only [doubleEdgeVertexQ,if_neg hb,if_neg hs,if_neg he]
          change (gridVertexQ F e.owner m e.p (e.i+1) (e.j+d)).2+40 ≤ R^9
          omega
  have hl : (localFaceEndpointsQ F m c).2≤ R^12 := by
    have h1 := pow_one_le R 9 (by omega)
    have hp := pow_constant R 9 3 8 hR (by decide)
    change 8*R^9≤R^12 at hp
    have hx := hgrid c.owner c.p (c.i+c.k) (c.j+c.l)
    have hq0 := (hedge c.owner c.p c.i (c.j+c.l)).1
    have hq1 := (hedge c.owner c.p (c.i+c.k) c.j).2
    have p89 : R^8≤ R^9 := pow_mono R (by omega) (by decide)
    have hx9 := hx.trans p89
    have hq09 := hq0.trans p89
    have hq19 := hq1.trans p89
    have h512 : 512≤ R^9 := (show 512≤2^9 by decide).trans (Nat.pow_le_pow_left hR 9)
    have h104 : 104≤ R^9 := (show 104≤2^9 by decide).trans (Nat.pow_le_pow_left hR 9)
    have he := hd {owner:=c.owner,copy:=c.k,part:=1,p:=c.p,q:=c.q,i:=c.i} c.l
    by_cases hc : c.part=0 <;>
      simp only [localFaceEndpointsQ,bridgeOfVertexQ,hc,ite_true,ite_false] <;> omega
  have hg : (glueFaceEndpointsQ F m c).2≤ R^12 := by
    let e : Code := {family:=1,owner:=c.p,copy:=c.copy,part:=c.part,p:=c.q,i:=c.i}
    have he := hd (qEdgeImageQ c.owner e).1 c.k
    have hq : (qDoubleEdgeVertexQ m e c.k).2≤64 := by
      by_cases h : e.part=1
      · simp only [qDoubleEdgeVertexQ,h,ite_true]; omega
      · simp only [qDoubleEdgeVertexQ,h,ite_false]; omega
    have hp : 8*R^9≤ R^12 := pow_constant R 9 3 8 hR (by decide)
    have hsmall : 184≤ R^9 := (show 184≤2^9 by decide).trans (Nat.pow_le_pow_left hR 9)
    change 48+(doubleEdgeVertexQ F m (qEdgeImageQ c.owner e).1 c.k).2+
      (qDoubleEdgeVertexQ m e c.k).2+72≤ R^12
    omega
  have ho : (oldFaceEndpointsQ F c).2≤ R^12 := by
    have hp : 512*R^3 ≤ R^12 := pow_constant R 3 9 512 hR (by decide)
    have h1 := pow_one_le R 3 (by omega)
    have hr := hread c.owner
    change (faceAtQ F.faces c.owner).2+136 ≤ R^12
    omega
  have hsmall : 5≤ R^12 := (show 5≤2^12 by decide).trans (Nat.pow_le_pow_left hR 12)
  have hlocal := pow_sum R 12 hR hl hsmall
  have hglue := pow_sum R 12 hR hg hsmall
  have hold := pow_sum R 12 hR ho hsmall
  by_cases h0 : c.family=0
  · simpa only [faceEndpointsQ,if_pos h0] using hlocal
  · by_cases h1 : c.family=1
    · simpa only [faceEndpointsQ,if_neg h0,if_pos h1] using hglue
    · simpa only [faceEndpointsQ,if_neg h0,if_neg h1] using hold
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
theorem _root_.solution (F : Frame) (m : ℕ) :
    (rxFrameQ F m).2≤(radius F m)^190 ∧ frameSize (rxFrameQ F m).1≤(radius F m)^88 := by
  let R := radius F m
  have hR : 2≤ R := radius_two F m
  have hb := rx_carrier_work F m
  have hf := rx_faces_work F m
  have hx := relax R hR (by decide : 63≤84) hb.1
  have hq := relax R hR (by decide : 75≤84) hb.2.1
  have hz := relax R hR (by decide : 68≤84) hb.2.2
  let xs := (dedupQ (rxXCodesQ F m).1).1
  let qs := (dedupQ (rxQCodesQ F m).1).1
  let zs := (dedupQ (rxZCodesQ F m).1).1
  let fs := (dedupQ (rxFaceCodesQ F m).1).1
  have lx : xs.length≤ R^84 := (dedupQ_length_le _).trans ((work_length _).trans hx)
  have lq : qs.length≤ R^84 := (dedupQ_length_le _).trans ((work_length _).trans hq)
  have lz : zs.length≤ R^84 := (dedupQ_length_le _).trans ((work_length _).trans hz)
  have lf : fs.length≤ R^84 := (dedupQ_length_le _).trans ((work_length _).trans hf)
  have dx := dedup_pow R hR 84 _ ((work_length _).trans hx)
  have dq := dedup_pow R hR 84 _ ((work_length _).trans hq)
  have dz := dedup_pow R hR 84 _ ((work_length _).trans hz)
  have df := dedup_pow R hR 84 _ ((work_length _).trans hf)
  norm_num only at dx dq dz df
  let rows := mapQ (fun c =>
    let points := faceEndpointsQ F m c
    let out := indexFaceQ xs qs zs c points.1
    (out.1,points.2+out.2)) fs
  have hc (c : Code) : (indexFaceQ xs qs zs c (faceEndpointsQ F m c).1).2≤ R^93 := by
    have a := handleQ_cost_le (faceEndpointsQ F m c).1.x xs
    have b := handleQ_cost_le (faceEndpointsQ F m c).1.z zs
    have d := handleQ_cost_le (faceEndpointsQ F m c).1.q0 qs
    have e := handleQ_cost_le (faceEndpointsQ F m c).1.q1 qs
    have hp := pow_constant R 84 9 512 hR (by decide)
    change 512*R^84≤R^93 at hp
    have h1 := pow_one_le R 84 (by omega)
    change (handleQ (faceEndpointsQ F m c).1.x xs).2+
      (handleQ (faceEndpointsQ F m c).1.z zs).2+
      (handleQ (faceEndpointsQ F m c).1.q0 qs).2+
      (handleQ (faceEndpointsQ F m c).1.q1 qs).2+7≤ R^93
    omega
  have hr : work rows≤ R^181 := map_pow R hR 84 94 _ fs lf (by
    intro c hcm
    have hp := endpoint_cost F m c
    have hi := hc c
    have hs := pow_sum R 93 hR (hp.trans (pow_mono R (by omega) (by decide))) hi
    exact hs)
  have hpack : (packFrameQ xs qs zs rows.1).2≤ R^88 := by
    have lp : rows.1.length=fs.length := mapQ_length _ fs
    have hp := pow_constant R 84 4 16 hR (by decide)
    change 16*R^84≤R^88 at hp
    have h1 := pow_one_le R 84 (by omega)
    have h2 : 2≤ R^84 := by
      exact (show 2≤2^84 by decide).trans (Nat.pow_le_pow_left hR 84)
    change xs.length+qs.length+zs.length+rows.1.length+13≤ R^88
    omega
  constructor
  · have h178 := pow_mono R (by omega) (by decide : 178≤181)
    have h84 := pow_mono R (by omega) (by decide : 84≤181)
    have h88 := pow_mono R (by omega) (by decide : 88≤181)
    have hp := pow_constant R 181 9 512 hR (by decide)
    change 512*R^181≤R^190 at hp
    have h1 := pow_one_le R 181 (by omega)
    have lx' := ((work_cost _).trans hx).trans h84
    have lq' := ((work_cost _).trans hq).trans h84
    have lz' := ((work_cost _).trans hz).trans h84
    have lf' := ((work_cost _).trans hf).trans h84
    have dx' := ((work_cost _).trans dx).trans h178
    have dq' := ((work_cost _).trans dq).trans h178
    have dz' := ((work_cost _).trans dz).trans h178
    have df' := ((work_cost _).trans df).trans h178
    have hr' := (work_cost _).trans hr
    have hp' := hpack.trans h88
    change (rxXCodesQ F m).2+(rxQCodesQ F m).2+(rxZCodesQ F m).2+
      (rxFaceCodesQ F m).2+(dedupQ (rxXCodesQ F m).1).2+
      (dedupQ (rxQCodesQ F m).1).2+(dedupQ (rxZCodesQ F m).1).2+
      (dedupQ (rxFaceCodesQ F m).1).2+rows.2+(packFrameQ xs qs zs rows.1).2+16≤ R^190
    omega
  · have lp : rows.1.length=fs.length := mapQ_length _ fs
    have hp := pow_constant R 84 4 16 hR (by decide)
    change 16*R^84≤R^88 at hp
    have h1 := pow_one_le R 84 (by omega)
    change frameSize (packFrameQ xs qs zs rows.1).1≤ R^88
    simp only [frameSize,packFrameQ]
    omega
end QEC.Coding.BDL26NativePresentationGenerator
