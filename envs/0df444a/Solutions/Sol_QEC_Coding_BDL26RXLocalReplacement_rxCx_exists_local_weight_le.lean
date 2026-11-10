-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:15:25.65621+00:00
-- url     : https://prove2.me/submissions/03ab4026-be80-4d1b-a187-caa458a172d1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_layer_parity
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_strip_parity
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_gauge_makes_pieces_even
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_even_pieces_cleanup
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_region_parity_budget
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
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_connectingWeight_zero
import Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_sum_pieceCrossingCost_le_of_first_layer
import Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_sum_pieceCrossingCost_le_of_second_layer
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
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
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
attribute [local simp] QEC.Coding.BDL26RXLocalReplacement.xLocalWordPush_single
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators
private theorem xLocalRegionParity_add
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (s t : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (region : Two ⊕ Two) :
    xLocalRegionParity P x S (s + t) face region =
      xLocalRegionParity P x S s face region + xLocalRegionParity P x S t face region := by
  cases region with
  | inl copy =>
      change totalParity (xLocalLayerWord P x S s face copy +
        xLocalLayerWord P x S t face copy) = _
      exact map_add _ _ _
  | inr side =>
      change totalParity (xLocalStripWord P x S s face side +
        xLocalStripWord P x S t face side) = _
      exact map_add _ _ _
private theorem xLocal_choose_gauge_budget
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (s : Word Field (DoubleCylinderFace P x S))
    (alpha : Neighbor P x → Field) :
    ∃ selected : Two,
      xLocalCrossingBudget P x S
        (s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) ≤ HammingWeight s := by
  classical
  let p := fun face region => xLocalRegionParity P x S s face region
  have horig := xLocal_region_parity_budget P A4 R x S s
  by_cases hLayer : (∑ face, bitWeight (p face (Sum.inl 1))) ≤
      ∑ face, bitWeight (p face (Sum.inl 0))
  · refine ⟨0, ?_⟩
    let tau := s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S 0 alpha)
    have h1 : ∀ face, xLocalRegionParity P x S tau face (Sum.inl 1) = p face (Sum.inl 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_layer_parity]
    have hl : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 0) = p face (Sum.inr 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hr : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 1) = p face (Sum.inr 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hcost := sum_pieceCrossingCost_le_of_second_layer
      (fun face => p face (Sum.inl 0)) (fun face => p face (Sum.inl 1))
      (fun face => xLocalRegionParity P x S tau face (Sum.inl 0))
      (fun face => p face (Sum.inr 0)) (fun face => p face (Sum.inr 1)) hLayer
    change xLocalCrossingBudget P x S tau ≤ HammingWeight s
    unfold xLocalCrossingBudget
    simp_rw [h1, hl, hr]
    exact hcost.trans horig
  · refine ⟨1, ?_⟩
    have hLayer' : (∑ face, bitWeight (p face (Sum.inl 0))) ≤
        ∑ face, bitWeight (p face (Sum.inl 1)) := by omega
    let tau := s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S 1 alpha)
    have h0 : ∀ face, xLocalRegionParity P x S tau face (Sum.inl 0) = p face (Sum.inl 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_layer_parity]
    have hl : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 0) = p face (Sum.inr 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hr : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 1) = p face (Sum.inr 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hcost := sum_pieceCrossingCost_le_of_first_layer
      (fun face => p face (Sum.inl 0)) (fun face => p face (Sum.inl 1))
      (fun face => xLocalRegionParity P x S tau face (Sum.inl 1))
      (fun face => p face (Sum.inr 0)) (fun face => p face (Sum.inr 1)) hLayer'
    change xLocalCrossingBudget P x S tau ≤ HammingWeight s
    unfold xLocalCrossingBudget
    simp_rw [h0, hl, hr]
    exact hcost.trans horig
private theorem xLocalCertificate_connectingWeight_add_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f g : Word Field (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S (f + g) ≤
      connectingWeight P A x S f + connectingWeight P A x S g := by
  unfold connectingWeight
  simp only [map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => HammingWeight_add_le _ _)
end QEC.Coding.BDL26RXLocalReplacement
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      connectingWeight P A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible x S f ≤
        HammingWeight syndrome := by
  classical
  obtain ⟨e, rfl⟩ := hs
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let D := wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
  let alpha := interfaceParity P A x S e
  obtain ⟨selected, hbudget⟩ := xLocal_choose_gauge_budget P A A4 R x S (D e) alpha
  let gauge := radialGauge P A x S selected alpha
  let tau := D e + D gauge
  have heven := fun face => xLocal_gauge_makes_pieces_even P A x S e selected face
  obtain ⟨cleanup, hcleanup, hweight⟩ :=
    xLocal_even_pieces_cleanup P A A4 R x S tau heven
  refine ⟨gauge + cleanup, ?_, ?_⟩
  · change D (gauge + cleanup) = D e
    rw [map_add, hcleanup]
    change D gauge + (D e + D gauge) = D e
    rw [add_left_comm, ZModModule.add_self, add_zero]
  · have hsum := xLocalCertificate_connectingWeight_add_le P A x S gauge cleanup
    have hzero : connectingWeight P A x S gauge = 0 :=
      radialGauge_connectingWeight_zero P A x S selected alpha
    change connectingWeight P A x S cleanup ≤ xLocalCrossingBudget P x S tau at hweight
    change xLocalCrossingBudget P x S tau ≤ HammingWeight (D e) at hbudget
    change connectingWeight P A x S (gauge + cleanup) ≤ HammingWeight (D e)
    omega
end QEC.Coding.BDL26RXLocalReplacement
