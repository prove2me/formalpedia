-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCxH1Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:46:26.060276+00:00
-- url     : https://prove2.me/submissions/49b5febd-327f-401c-ba6e-6ef711b4a58c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxH1_qzTerminal_equation
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_finSuccGrid_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionCoboundary_squared
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
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderEndInclusion_apply
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
namespace QEC
namespace Coding
namespace BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
private theorem rxSum_mul_indicator {Index : Type} [Fintype Index]
    [DecidableEq Index] (word : Index → Field) (target : Index) :
    (∑ index : Index, word index * if index = target then 1 else 0) =
      word target := by
  simp
private theorem rxSum_product_fst_indicator {Tag Index : Type}
    [Fintype Tag] [DecidableEq Tag] [Fintype Index]
    (word : Tag × Index → Field) (tag : Tag) (coefficient : Index → Field) :
    (∑ pair : Tag × Index,
        word pair * if pair.1 = tag then coefficient pair.2 else 0) =
      ∑ index : Index, word (tag, index) * coefficient index := by
  classical
  simp [Fintype.sum_prod_type, mul_ite]
private theorem rxSum_mul_four_indicators {Index : Type} [Fintype Index]
    [DecidableEq Index] (word : Index → Field) (first second third fourth : Index) :
    (∑ index : Index, word index *
      ((((if index = first then 1 else 0) +
          (if index = second then 1 else 0)) +
        (if index = third then 1 else 0)) +
        (if index = fourth then 1 else 0))) =
      word first + word second + word third + word fourth := by
  simp only [mul_add, Finset.sum_add_distrib, rxSum_mul_indicator]
private theorem rxSum_mul_two_indicators {Index : Type} [Fintype Index]
    [DecidableEq Index] (word : Index → Field) (first second : Index) :
    (∑ index : Index, word index *
      ((if index = first then 1 else 0) +
        (if index = second then 1 else 0))) =
      word first + word second := by
  simp only [mul_add, Finset.sum_add_distrib, rxSum_mul_indicator]
private theorem rxCxH1_smallSquare_sum_eq_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : SubdivisionFace P x S) :
    word (Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face (0, 0))) +
        word (Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face (1, 1))) +
        word (Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face (0, 1))) +
        word (Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face (1, 0))) =
      0 := by
  classical
  have hface := congrFun hword (Sum.inl (copy, face))
  change wordLinearMapTranspose
      (Matrix.toLin' (doubleCylinderFaceEdgeMatrix P x S)) word
        (Sum.inl (copy, face)) = 0 at hface
  rw [wordLinearMapTranspose_toLin'_apply] at hface
  rw [Fintype.sum_sum_type] at hface
  simp only [doubleCylinderFaceEdgeMatrix, mul_zero,
    Finset.sum_const_zero, add_zero] at hface
  have hproduct :
      (∑ pair : Two × SubdivisionEdge P x S,
        word (Sum.inl pair) * if pair.1 = copy then
          subdivisionFaceEdgeMatrix P x S pair.2 face else 0) =
        ∑ edge : SubdivisionEdge P x S,
          word (Sum.inl (copy, edge)) *
            subdivisionFaceEdgeMatrix P x S edge face := by
    exact rxSum_product_fst_indicator
      (fun pair : Two × SubdivisionEdge P x S => word (Sum.inl pair)) copy
      (fun edge => subdivisionFaceEdgeMatrix P x S edge face)
  have hfour := rxSum_mul_four_indicators
    (fun edge : SubdivisionEdge P x S => word (Sum.inl (copy, edge)))
    (subdivisionFaceBoundaryEdge P x S face (0, 0))
    (subdivisionFaceBoundaryEdge P x S face (1, 1))
    (subdivisionFaceBoundaryEdge P x S face (0, 1))
    (subdivisionFaceBoundaryEdge P x S face (1, 0))
  rw [← hfour]
  change (∑ edge : SubdivisionEdge P x S,
      word (Sum.inl (copy, edge)) *
        subdivisionFaceEdgeMatrix P x S edge face) = 0
  rw [← hproduct]
  exact hface
private theorem rxCxH1_potential_smallSquare_sum_eq_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (potential : Word Field (SubdivisionVertex P x S))
    (face : SubdivisionFace P x S) :
    let value := fun edge : SubdivisionEdge P x S =>
      potential (subdivisionEdgeStart P x S edge) +
        potential (subdivisionEdgeEnd P x S edge)
    value (subdivisionFaceBoundaryEdge P x S face (0, 0)) +
        value (subdivisionFaceBoundaryEdge P x S face (1, 1)) +
      value (subdivisionFaceBoundaryEdge P x S face (0, 1)) +
        value (subdivisionFaceBoundaryEdge P x S face (1, 0)) = 0 := by
  classical
  dsimp only
  let coboundary := wordLinearMapTranspose
    (subdivisionBoundary1 P x S) potential
  have hedge (edge : SubdivisionEdge P x S) :
      coboundary edge =
        potential (subdivisionEdgeStart P x S edge) +
          potential (subdivisionEdgeEnd P x S edge) := by
    rw [show coboundary edge = wordLinearMapTranspose
      (subdivisionBoundary1 P x S) potential edge from rfl]
    rw [subdivisionBoundary1, wordLinearMapTranspose_toLin'_apply]
    change (∑ vertex : SubdivisionVertex P x S,
      potential vertex *
        ((if vertex = subdivisionEdgeStart P x S edge then 1 else 0) +
          (if vertex = subdivisionEdgeEnd P x S edge then 1 else 0))) = _
    exact rxSum_mul_two_indicators potential
      (subdivisionEdgeStart P x S edge)
      (subdivisionEdgeEnd P x S edge)
  have hsquared := congrArg (fun map => map potential)
    (subdivisionCoboundary_squared P x S)
  have hface := congrFun hsquared face
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply] at hface
  change wordLinearMapTranspose (subdivisionBoundary2 P x S)
      coboundary face = 0 at hface
  rw [subdivisionBoundary2, wordLinearMapTranspose_toLin'_apply] at hface
  have hfour := rxSum_mul_four_indicators coboundary
    (subdivisionFaceBoundaryEdge P x S face (0, 0))
    (subdivisionFaceBoundaryEdge P x S face (1, 1))
    (subdivisionFaceBoundaryEdge P x S face (0, 1))
    (subdivisionFaceBoundaryEdge P x S face (1, 0))
  rw [← hedge (subdivisionFaceBoundaryEdge P x S face (0, 0)),
    ← hedge (subdivisionFaceBoundaryEdge P x S face (1, 1)),
    ← hedge (subdivisionFaceBoundaryEdge P x S face (0, 1)),
    ← hedge (subdivisionFaceBoundaryEdge P x S face (1, 0))]
  rw [← hfour]
  change (∑ edge : SubdivisionEdge P x S,
    coboundary edge * subdivisionFaceEdgeMatrix P x S edge face) = 0
  exact hface
private theorem rxCxH1_smallSquare_curl_transport
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (potential : Word Field (SubdivisionVertex P x S))
    (face : SubdivisionFace P x S)
    (hbottom :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 0))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 0))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (0, 0))))
    (hright :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 1))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 1))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (1, 1))))
    (hleft :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 0))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 0))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (1, 0)))) :
    potential (subdivisionEdgeStart P x S
        (subdivisionFaceBoundaryEdge P x S face (0, 1))) +
      potential (subdivisionEdgeEnd P x S
        (subdivisionFaceBoundaryEdge P x S face (0, 1))) =
      word (Sum.inl (copy,
        subdivisionFaceBoundaryEdge P x S face (0, 1))) := by
  have hpotential := rxCxH1_potential_smallSquare_sum_eq_zero
    P x S potential face
  have hcocycle := rxCxH1_smallSquare_sum_eq_zero
    P x S word hword copy face
  dsimp only at hpotential
  rw [hbottom, hright, hleft] at hpotential
  linear_combination hpotential - hcocycle
private theorem rxCxH1_smallSquare_curl_transport_right
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (potential : Word Field (SubdivisionVertex P x S))
    (face : SubdivisionFace P x S)
    (hbottom :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 0))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 0))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (0, 0))))
    (htop :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 1))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (0, 1))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (0, 1))))
    (hleft :
      potential (subdivisionEdgeStart P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 0))) +
        potential (subdivisionEdgeEnd P x S
          (subdivisionFaceBoundaryEdge P x S face (1, 0))) =
        word (Sum.inl (copy,
          subdivisionFaceBoundaryEdge P x S face (1, 0)))) :
    potential (subdivisionEdgeStart P x S
        (subdivisionFaceBoundaryEdge P x S face (1, 1))) +
      potential (subdivisionEdgeEnd P x S
        (subdivisionFaceBoundaryEdge P x S face (1, 1))) =
      word (Sum.inl (copy,
        subdivisionFaceBoundaryEdge P x S face (1, 1))) := by
  have hpotential := rxCxH1_potential_smallSquare_sum_eq_zero
    P x S potential face
  have hcocycle := rxCxH1_smallSquare_sum_eq_zero
    P x S word hword copy face
  dsimp only at hpotential
  rw [hbottom, htop, hleft] at hpotential
  linear_combination hpotential - hcocycle
private theorem rxCxH1_rectangle_sum_eq_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    word (doubleCylinderRectangleBoundaryEdge P x S rectangle (0, 0)) +
        word (doubleCylinderRectangleBoundaryEdge P x S rectangle (0, 1)) +
        word (doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 0)) +
        word (doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 1)) =
      0 := by
  classical
  have hface := congrFun hword (Sum.inr rectangle)
  change wordLinearMapTranspose
      (Matrix.toLin' (doubleCylinderFaceEdgeMatrix P x S)) word
        (Sum.inr rectangle) = 0 at hface
  rw [wordLinearMapTranspose_toLin'_apply] at hface
  rw [Fintype.sum_sum_type] at hface
  simp only [doubleCylinderFaceEdgeMatrix] at hface
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hface
  simp only [if_true, mul_one] at hface
  simp only [rxSum_mul_indicator] at hface
  have hvertical := rxSum_mul_two_indicators
    (fun vertex : SubdivisionBoundaryVertex P x S => word (Sum.inr vertex))
    (subdivisionBoundaryEdgeStart P x S rectangle)
    (subdivisionBoundaryEdgeEnd P x S rectangle)
  simp only [
    doubleCylinderRectangleBoundaryEdge_zero,
    doubleCylinderRectangleBoundaryEdge_one_zero,
    doubleCylinderRectangleBoundaryEdge_one_one]
  rw [add_assoc]
  rw [← hvertical]
  convert hface using 1
  congr 1
  apply Finset.sum_congr rfl
  intro vertex _
  by_cases hstart : vertex = subdivisionBoundaryEdgeStart P x S rectangle <;>
    by_cases hend : vertex = subdivisionBoundaryEdgeEnd P x S rectangle <;>
    simp [hstart, hend]
private theorem rxCxH1_cancel_successive (base accumulated edgeValue : Field) :
    (base + accumulated) + (base + (accumulated + edgeValue)) = edgeValue := by
  rw [show (base + accumulated) + (base + (accumulated + edgeValue)) =
      (base + base) + (accumulated + accumulated) + edgeValue by abel]
  rw [ZModModule.add_self, ZModModule.add_self]
  simp
private theorem rxCxH1_segmentInterior_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (edge : XStarEdge P x) (segment : Fin S.half)
    (hinterior : segment.1 + 1 < S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S edge segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S edge segment) =
      word (Sum.inl (copy, Sum.inl (edge, segment))) := by
  rcases segment with ⟨segment, hsegment⟩
  rcases segment with _ | segment
  · change 1 < S.half at hinterior
    have hnotlast : 1 ≠ S.half := by omega
    simp only [subdivisionSegmentStart, subdivisionSegmentEnd,
      dif_neg hnotlast, rxCxH1_subdivisionPotential,
      rxCxH1_segmentPrefix]
    change rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeStart P x edge) +
        (rxCxH1_oldVertexPotential P A3 x S word copy
            (xStarEdgeStart P x edge) +
          (0 + word (Sum.inl (copy, Sum.inl (edge, ⟨0, hsegment⟩))))) =
      word (Sum.inl (copy, Sum.inl (edge, ⟨0, hsegment⟩)))
    simpa using rxCxH1_cancel_successive
      (rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x edge)) 0
      (word (Sum.inl (copy, Sum.inl (edge, ⟨0, hsegment⟩))))
  · change segment + 2 < S.half at hinterior
    have hnotlast : segment + 2 ≠ S.half := by omega
    have hnotzero : segment + 1 ≠ 0 := by omega
    simp only [subdivisionSegmentStart, subdivisionSegmentEnd,
      dif_neg hnotzero, dif_neg hnotlast, rxCxH1_subdivisionPotential]
    change
      (rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeStart P x edge) +
        rxCxH1_segmentPrefix P x S word copy edge (segment + 1) (by omega)) +
      (rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeStart P x edge) +
        (rxCxH1_segmentPrefix P x S word copy edge (segment + 1) (by omega) +
          word (Sum.inl (copy, Sum.inl (edge, ⟨segment + 1, hsegment⟩))))) =
      word (Sum.inl (copy, Sum.inl (edge, ⟨segment + 1, hsegment⟩)))
    exact rxCxH1_cancel_successive
      (rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x edge))
      (rxCxH1_segmentPrefix P x S word copy edge (segment + 1) (by omega))
      (word (Sum.inl (copy, Sum.inl (edge, ⟨segment + 1, hsegment⟩))))
private theorem rxCxH1_horizontalPrefix_eq_xqZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) :
    (step : Nat) → (hstep : step ≤ S.half) →
      rxCxH1_horizontalPrefix P x S word copy face step hstep =
        rxCxH1_segmentPrefix P x S word copy
          (xStarFaceXQEdge P x face 0) step hstep
  | 0, _ => rfl
  | step + 1, hstep => by
      rw [rxCxH1_horizontalPrefix, rxCxH1_segmentPrefix,
        rxCxH1_horizontalPrefix_eq_xqZero P x S word copy face step]
      congr 3
private theorem rxCxH1_verticalInterior_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (i : Fin (S.half - 1))
    (segment : Fin S.half) (hpositive : 0 < segment.1)
    (hinterior : segment.1 + 1 < S.half) :
    let horizontal : Fin (S.half + 1) := ⟨i.1 + 1, by
      have := i.2
      have := S.half_pos
      omega⟩
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) =
      word (Sum.inl (copy,
        subdivisionVerticalEdge P x S face horizontal segment)) := by
  dsimp only
  rcases segment with ⟨segment, hsegment⟩
  rcases segment with _ | segment
  · change 0 < 0 at hpositive
    omega
  · change segment + 2 < S.half at hinterior
    have hhorizontalZero : i.1 + 1 ≠ 0 := by omega
    have hhorizontalLast : i.1 + 1 ≠ S.half := by
      have := i.2
      omega
    have hverticalZero : segment + 1 ≠ 0 := by omega
    have hverticalLast : segment + 1 ≠ S.half := by omega
    have hverticalSuccZero : segment + 2 ≠ 0 := by omega
    have hverticalSuccLast : segment + 2 ≠ S.half := by omega
    have hstart :
        subdivisionEdgeStart P x S
            (subdivisionVerticalEdge P x S face
              ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
              ⟨segment + 1, hsegment⟩) =
          Sum.inr (Sum.inr (face, i,
            (⟨segment, by omega⟩ : Fin (S.half - 1)))) := by
      rw [subdivisionVerticalEdge_start]
      change subdivisionGridVertex P x S face
          ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
          ⟨segment + 1, by omega⟩ = _
      simp only [subdivisionGridVertex, hhorizontalZero, hhorizontalLast,
        hverticalZero, hverticalLast, ↓reduceDIte]
      constructor <;> apply Fin.ext <;> rfl
    have hend :
        subdivisionEdgeEnd P x S
            (subdivisionVerticalEdge P x S face
              ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
              ⟨segment + 1, hsegment⟩) =
          Sum.inr (Sum.inr (face, i,
            (⟨segment + 1, by omega⟩ : Fin (S.half - 1)))) := by
      rw [subdivisionVerticalEdge_end]
      change subdivisionGridVertex P x S face
          ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
          ⟨segment + 2, by omega⟩ = _
      simp only [subdivisionGridVertex, hhorizontalZero, hhorizontalLast,
        hverticalSuccZero, hverticalSuccLast, ↓reduceDIte]
      constructor <;> apply Fin.ext <;> rfl
    rw [hstart, hend]
    simp only [rxCxH1_subdivisionPotential]
    change
      (rxCxH1_horizontalPrefix P x S word copy face (i.1 + 1) (by omega) +
        rxCxH1_verticalPrefix P x S word copy face
          ⟨i.1 + 1, by omega⟩ (segment + 1) (by omega)) +
      (rxCxH1_horizontalPrefix P x S word copy face (i.1 + 1) (by omega) +
        (rxCxH1_verticalPrefix P x S word copy face
            ⟨i.1 + 1, by omega⟩ (segment + 1) (by omega) +
          word (Sum.inl (copy, subdivisionVerticalEdge P x S face
            ⟨i.1 + 1, by omega⟩ ⟨segment + 1, hsegment⟩)))) =
      word (Sum.inl (copy, subdivisionVerticalEdge P x S face
        ⟨i.1 + 1, by omega⟩ ⟨segment + 1, hsegment⟩))
    exact rxCxH1_cancel_successive
      (rxCxH1_horizontalPrefix P x S word copy face (i.1 + 1) (by omega))
      (rxCxH1_verticalPrefix P x S word copy face
        ⟨i.1 + 1, by omega⟩ (segment + 1) (by omega))
      (word (Sum.inl (copy, subdivisionVerticalEdge P x S face
        ⟨i.1 + 1, by omega⟩ ⟨segment + 1, hsegment⟩)))
private theorem rxCxH1_horizontalBottom_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (segment : Fin S.half)
    (hnonterminal : segment.1 + 1 < S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionHorizontalEdge P x S face segment 0)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionHorizontalEdge P x S face segment 0)) =
      word (Sum.inl (copy,
        subdivisionHorizontalEdge P x S face segment 0)) := by
  simpa [subdivisionHorizontalEdge, subdivisionEdgeStart, subdivisionEdgeEnd] using
    rxCxH1_segmentInterior_equation P A3 x S word copy
      (xStarFaceXQEdge P x face 0) segment hnonterminal
private theorem rxCxH1_oldVertexPotential_xStarFaceXVertex
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) :
    rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarFaceXVertex P x face) = 0 := by
  rfl
private theorem rxCxH1_verticalBottom_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (i : Fin (S.half - 1)) :
    let horizontal : Fin (S.half + 1) := ⟨i.1 + 1, by
      have := i.2
      have := S.half_pos
      omega⟩
    let segment : Fin S.half := ⟨0, by have := i.2; omega⟩
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) =
      word (Sum.inl (copy,
        subdivisionVerticalEdge P x S face horizontal segment)) := by
  dsimp only
  have hhorizontalZero : i.1 + 1 ≠ 0 := by omega
  have hhorizontalLast : i.1 + 1 ≠ S.half := by
    have := i.2
    omega
  have honeLast : 1 ≠ S.half := by have := i.2; omega
  let zeroIndex : Fin (S.half - 1) := ⟨0, by have := i.2; omega⟩
  have hstart :
      subdivisionEdgeStart P x S
          (subdivisionVerticalEdge P x S face
            ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
            ⟨0, by have := i.2; omega⟩) =
        Sum.inr (Sum.inl (xStarFaceXQEdge P x face 0, i)) := by
    rw [subdivisionVerticalEdge_start]
    change subdivisionGridVertex P x S face
      ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩ 0 = _
    exact subdivisionGridVertex_edgeInterior_xq0 P x S face i
  have hend :
      subdivisionEdgeEnd P x S
          (subdivisionVerticalEdge P x S face
            ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
            ⟨0, by have := i.2; omega⟩) =
        Sum.inr (Sum.inr (face, i, zeroIndex)) := by
    rw [subdivisionVerticalEdge_end]
    change subdivisionGridVertex P x S face
      ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
      ⟨1, by have := i.2; omega⟩ = _
    simp only [subdivisionGridVertex, hhorizontalZero, hhorizontalLast,
      one_ne_zero, honeLast, ↓reduceDIte]
    dsimp only [zeroIndex]
    constructor <;> apply Fin.ext <;> rfl
  rw [hstart, hend]
  simp only [rxCxH1_subdivisionPotential]
  rw [xStarEdgeStart_faceXQEdge]
  rw [rxCxH1_oldVertexPotential_xStarFaceXVertex]
  rw [← rxCxH1_horizontalPrefix_eq_xqZero]
  simp only [zeroIndex, rxCxH1_verticalPrefix]
  simpa using rxCxH1_cancel_successive
    (rxCxH1_horizontalPrefix P x S word copy face
      (i.1 + 1) (by omega)) 0
    (word (Sum.inl (copy, subdivisionVerticalEdge P x S face
      ⟨i.1 + 1, by omega⟩ ⟨0, by omega⟩)))
private theorem rxCxH1_qRadialEdge_faceXQEdge
    (P : TannerSquarePresentation) (x : P.X) (face : XStarFace P x)
    (corner : Two) :
    rxCxH1_qRadialEdge P x (P.faceQ face.1 corner)
        (xStarFaceQVertex P x face corner).2 =
      xStarFaceXQEdge P x face corner := by
  apply Subtype.ext
  change Sum.inl
      (⟨(x, P.faceQ face.1 corner),
        rxCxH1_qIncidence P x (P.faceQ face.1 corner)
          (xStarFaceQVertex P x face corner).2⟩ : XQEdge P) =
    Sum.inl (faceXQEdge P face.1 corner)
  congr 1
  apply Subtype.ext
  have hx : P.faceX face.1 = x := by
    simpa [xStarFaceMember] using face.2
  change (x, P.faceQ face.1 corner) =
    (P.faceX face.1, P.faceQ face.1 corner)
  simp [hx]
private theorem rxCxH1_oldVertexPotential_faceQ
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (corner : Two) :
    rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarFaceQVertex P x face corner) =
      rxCxH1_segmentPrefix P x S word copy
        (xStarFaceXQEdge P x face corner) S.half (le_refl S.half) := by
  change rxCxH1_qPotential P x S word copy (P.faceQ face.1 corner)
      (xStarFaceQVertex P x face corner).2 = _
  dsimp only [rxCxH1_qPotential]
  rw [rxCxH1_qRadialEdge_faceXQEdge]
private theorem rxCxH1_xqTerminal_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (corner : Two)
    (segment : Fin S.half) (hterminal : segment.1 + 1 = S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceXQEdge P x face corner) segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceXQEdge P x face corner) segment) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceXQEdge P x face corner, segment))) := by
  have hlast : segment.1 + 1 = S.half := hterminal
  rcases segment with ⟨segment, hsegment⟩
  rcases segment with _ | segment
  · change 1 = S.half at hterminal
    have hstart : subdivisionSegmentStart P x S
        (xStarFaceXQEdge P x face corner) ⟨0, hsegment⟩ =
        Sum.inl (xStarEdgeStart P x (xStarFaceXQEdge P x face corner)) := by
      simp [subdivisionSegmentStart]
    have hend : subdivisionSegmentEnd P x S
        (xStarFaceXQEdge P x face corner) ⟨0, hsegment⟩ =
        Sum.inl (xStarEdgeEnd P x (xStarFaceXQEdge P x face corner)) := by
      simp [subdivisionSegmentEnd, hterminal]
    rw [hstart, hend]
    simp only [rxCxH1_subdivisionPotential]
    rw [xStarEdgeStart_faceXQEdge, xStarEdgeEnd_faceXQEdge,
      rxCxH1_oldVertexPotential_xStarFaceXVertex,
      rxCxH1_oldVertexPotential_faceQ]
    have hprefixFull :
        rxCxH1_segmentPrefix P x S word copy
            (xStarFaceXQEdge P x face corner) S.half (le_refl S.half) =
          rxCxH1_segmentPrefix P x S word copy
            (xStarFaceXQEdge P x face corner) 1 (by omega) := by
      congr 1
      exact hterminal.symm
    rw [hprefixFull, rxCxH1_segmentPrefix]
    simp [rxCxH1_segmentPrefix]
  · change segment + 2 = S.half at hterminal
    have hnotzero : segment + 1 ≠ 0 := by omega
    let interior : Fin (S.half - 1) := ⟨segment, by omega⟩
    have hstart : subdivisionSegmentStart P x S
        (xStarFaceXQEdge P x face corner) ⟨segment + 1, hsegment⟩ =
        Sum.inr (Sum.inl
          (xStarFaceXQEdge P x face corner, interior)) := by
      simp [subdivisionSegmentStart, hnotzero, interior]
    have hend : subdivisionSegmentEnd P x S
        (xStarFaceXQEdge P x face corner) ⟨segment + 1, hsegment⟩ =
        Sum.inl (xStarEdgeEnd P x (xStarFaceXQEdge P x face corner)) := by
      simp [subdivisionSegmentEnd, hterminal]
    rw [hstart, hend]
    simp only [rxCxH1_subdivisionPotential]
    rw [xStarEdgeEnd_faceXQEdge, rxCxH1_oldVertexPotential_faceQ]
    rw [xStarEdgeStart_faceXQEdge,
      rxCxH1_oldVertexPotential_xStarFaceXVertex]
    have hprefixFull :
        rxCxH1_segmentPrefix P x S word copy
            (xStarFaceXQEdge P x face corner) S.half (le_refl S.half) =
          rxCxH1_segmentPrefix P x S word copy
            (xStarFaceXQEdge P x face corner) (segment + 2) (by omega) := by
      congr 1
      exact hterminal.symm
    rw [hprefixFull]
    rw (occs := .pos [2]) [rxCxH1_segmentPrefix]
    dsimp only [interior]
    simpa using rxCxH1_cancel_successive
      0
      (rxCxH1_segmentPrefix P x S word copy
        (xStarFaceXQEdge P x face corner) (segment + 1) (by omega))
      (word (Sum.inl (copy, Sum.inl
        (xStarFaceXQEdge P x face corner, ⟨segment + 1, hsegment⟩))))
private theorem rxCxH1_horizontalBottom_total_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (segment : Fin S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionHorizontalEdge P x S face segment 0)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionHorizontalEdge P x S face segment 0)) =
      word (Sum.inl (copy,
        subdivisionHorizontalEdge P x S face segment 0)) := by
  by_cases hterminal : segment.1 + 1 = S.half
  · simpa [subdivisionHorizontalEdge, subdivisionEdgeStart, subdivisionEdgeEnd] using
      rxCxH1_xqTerminal_equation P A3 x S word copy face 0
        segment hterminal
  · exact rxCxH1_horizontalBottom_equation P A3 x S word copy face
      segment (by have := segment.2; omega)
private theorem rxCxH1_verticalNonterminal_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (horizontal : Fin (S.half + 1))
    (segment : Fin S.half) (hnonterminal : segment.1 + 1 < S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionVerticalEdge P x S face horizontal segment)) =
      word (Sum.inl (copy,
        subdivisionVerticalEdge P x S face horizontal segment)) := by
  by_cases hzero : horizontal.1 = 0
  · have horizontalZero : horizontal = 0 := by
      apply Fin.ext
      exact hzero
    subst horizontal
    simpa [subdivisionVerticalEdge, subdivisionEdgeStart, subdivisionEdgeEnd] using
      rxCxH1_segmentInterior_equation P A3 x S word copy
        (xStarFaceXQEdge P x face 1) segment hnonterminal
  · by_cases hlast : horizontal.1 = S.half
    · have horizontalLast : horizontal = ⟨S.half, by omega⟩ := by
        apply Fin.ext
        exact hlast
      have hhalf : S.half ≠ 0 := by omega
      rw [horizontalLast]
      simpa [subdivisionVerticalEdge, hhalf, subdivisionEdgeStart, subdivisionEdgeEnd] using
        rxCxH1_segmentInterior_equation P A3 x S word copy
          (xStarFaceQZEdge P x face 0) segment hnonterminal
    · let interior : Fin (S.half - 1) :=
        ⟨horizontal.1 - 1, by
          have hbound := horizontal.2
          omega⟩
      have hinteriorSucc : interior.1 + 1 = horizontal.1 := by
        dsimp only [interior]
        omega
      rcases segment with ⟨segment, hsegment⟩
      rcases segment with _ | segment
      · simpa [subdivisionVerticalEdge, hzero, hlast, interior,
          hinteriorSucc] using
          rxCxH1_verticalBottom_equation P A3 x S word copy face interior
      · change segment + 2 < S.half at hnonterminal
        have hsegmentFin : segment + 1 < S.half := by omega
        simpa [subdivisionVerticalEdge, hzero, hlast, interior,
            hinteriorSucc] using
          rxCxH1_verticalInterior_equation P A3 x S word copy face interior
            ⟨segment + 1, hsegmentFin⟩ (Nat.zero_lt_succ segment)
            hnonterminal
private theorem rxCxH1_horizontalLower_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x) (segment : Fin S.half) :
    (row : Nat) → (hrow : row < S.half) →
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionHorizontalEdge P x S face segment
              ⟨row, by omega⟩)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionHorizontalEdge P x S face segment
              ⟨row, by omega⟩)) =
        word (Sum.inl (copy,
          subdivisionHorizontalEdge P x S face segment
            ⟨row, by omega⟩))
  | 0, _ => rxCxH1_horizontalBottom_total_equation
      P A3 x S word copy face segment
  | row + 1, hrow => by
      let cell : SubdivisionFace P x S :=
        (face, segment, ⟨row, by omega⟩)
      let potential : Word Field (SubdivisionVertex P x S) :=
        rxCxH1_subdivisionPotential P A3 x S word copy
      apply rxCxH1_smallSquare_curl_transport
        P x S word hword copy potential cell
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionHorizontalEdge P x S face segment
                  ⟨row, by omega⟩)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionHorizontalEdge P x S face segment
                  ⟨row, by omega⟩)) =
            word (Sum.inl (copy,
              subdivisionHorizontalEdge P x S face segment
                ⟨row, by omega⟩))
        exact rxCxH1_horizontalLower_equation P A3 x S word hword copy
          face segment row (by omega)
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionVerticalEdge P x S face
                  ⟨segment.1 + 1, by omega⟩ ⟨row, by omega⟩)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionVerticalEdge P x S face
                  ⟨segment.1 + 1, by omega⟩ ⟨row, by omega⟩)) =
            word (Sum.inl (copy, subdivisionVerticalEdge P x S face
              ⟨segment.1 + 1, by omega⟩ ⟨row, by omega⟩))
        exact rxCxH1_verticalNonterminal_equation P A3 x S word copy face
          ⟨segment.1 + 1, by omega⟩ ⟨row, by omega⟩ hrow
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionVerticalEdge P x S face
                  ⟨segment.1, by omega⟩ ⟨row, by omega⟩)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionVerticalEdge P x S face
                  ⟨segment.1, by omega⟩ ⟨row, by omega⟩)) =
            word (Sum.inl (copy, subdivisionVerticalEdge P x S face
              ⟨segment.1, by omega⟩ ⟨row, by omega⟩))
        exact rxCxH1_verticalNonterminal_equation P A3 x S word copy face
          ⟨segment.1, by omega⟩ ⟨row, by omega⟩ hrow
private theorem rxCxH1_verticalTerminalInterior_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x) :
    (column : Nat) → (hcolumn : column + 1 < S.half) →
      let terminal : Fin S.half := ⟨S.half - 1, by omega⟩
      let horizontal : Fin (S.half + 1) := ⟨column + 1, by omega⟩
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionVerticalEdge P x S face horizontal terminal)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionVerticalEdge P x S face horizontal terminal)) =
        word (Sum.inl (copy,
          subdivisionVerticalEdge P x S face horizontal terminal)) := by
  intro column hcolumn
  induction column with
  | zero =>
      dsimp only
      let terminal : Fin S.half := ⟨S.half - 1, by omega⟩
      let cell : SubdivisionFace P x S :=
        (face, ⟨0, by omega⟩, terminal)
      let potential : Word Field (SubdivisionVertex P x S) :=
        rxCxH1_subdivisionPotential P A3 x S word copy
      apply rxCxH1_smallSquare_curl_transport_right
        P x S word hword copy potential cell
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionHorizontalEdge P x S face ⟨0, by omega⟩
                  ⟨S.half - 1, by omega⟩)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionHorizontalEdge P x S face ⟨0, by omega⟩
                  ⟨S.half - 1, by omega⟩)) =
            word (Sum.inl (copy, subdivisionHorizontalEdge P x S face
              ⟨0, by omega⟩ ⟨S.half - 1, by omega⟩))
        exact rxCxH1_horizontalLower_equation P A3 x S word hword copy
          face ⟨0, by omega⟩ (S.half - 1) (by omega)
      · have htopEdge :
            subdivisionFaceBoundaryEdge P x S cell (0, 1) =
              subdivisionHorizontalEdge P x S face ⟨0, by omega⟩
                ⟨S.half, by omega⟩ := by
          rw [subdivisionFaceBoundaryEdge_zero_one]
          congr 1
          apply Fin.ext
          rw [finSuccGrid_val]
          dsimp only [cell, terminal]
          omega
        rw [htopEdge]
        dsimp only [potential]
        have hhalf : S.half ≠ 0 := by omega
        simpa [subdivisionHorizontalEdge, hhalf, subdivisionEdgeStart, subdivisionEdgeEnd] using
          rxCxH1_segmentInterior_equation P A3 x S word copy
            (xStarFaceQZEdge P x face 1) ⟨0, by omega⟩ hcolumn
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionVerticalEdge P x S face 0 terminal)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionVerticalEdge P x S face 0 terminal)) =
            word (Sum.inl (copy, subdivisionVerticalEdge P x S face 0 terminal))
        simpa [subdivisionVerticalEdge, subdivisionEdgeStart, subdivisionEdgeEnd] using
          rxCxH1_xqTerminal_equation P A3 x S word copy face 1 terminal
            (by dsimp only [terminal]; omega)
  | succ column ih =>
      dsimp only
      let terminal : Fin S.half := ⟨S.half - 1, by omega⟩
      let segment : Fin S.half := ⟨column + 1, by omega⟩
      let cell : SubdivisionFace P x S := (face, segment, terminal)
      let potential : Word Field (SubdivisionVertex P x S) :=
        rxCxH1_subdivisionPotential P A3 x S word copy
      apply rxCxH1_smallSquare_curl_transport_right
        P x S word hword copy potential cell
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionHorizontalEdge P x S face segment
                  ⟨S.half - 1, by omega⟩)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionHorizontalEdge P x S face segment
                  ⟨S.half - 1, by omega⟩)) =
            word (Sum.inl (copy, subdivisionHorizontalEdge P x S face
              segment ⟨S.half - 1, by omega⟩))
        exact rxCxH1_horizontalLower_equation P A3 x S word hword copy
          face segment (S.half - 1) (by omega)
      · have htopEdge :
            subdivisionFaceBoundaryEdge P x S cell (0, 1) =
              subdivisionHorizontalEdge P x S face segment
                ⟨S.half, by omega⟩ := by
          rw [subdivisionFaceBoundaryEdge_zero_one]
          congr 1
          apply Fin.ext
          rw [finSuccGrid_val]
          dsimp only [cell, terminal]
          omega
        rw [htopEdge]
        dsimp only [potential]
        have hhalf : S.half ≠ 0 := by omega
        simpa [subdivisionHorizontalEdge, segment, hhalf,
          subdivisionEdgeStart, subdivisionEdgeEnd] using
          rxCxH1_segmentInterior_equation P A3 x S word copy
            (xStarFaceQZEdge P x face 1) segment hcolumn
      · change
          rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeStart P x S
                (subdivisionVerticalEdge P x S face
                  ⟨column + 1, by omega⟩ terminal)) +
            rxCxH1_subdivisionPotential P A3 x S word copy
              (subdivisionEdgeEnd P x S
                (subdivisionVerticalEdge P x S face
                  ⟨column + 1, by omega⟩ terminal)) =
            word (Sum.inl (copy, subdivisionVerticalEdge P x S face
              ⟨column + 1, by omega⟩ terminal))
        exact ih (by omega)
private theorem rxCxH1_starEdgeTerminal_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (edge : XStarEdge P x) (segment : Fin S.half)
    (hterminal : segment.1 + 1 = S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S edge segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S edge segment) =
      word (Sum.inl (copy, Sum.inl (edge, segment))) := by
  rcases edge with ⟨rawEdge, member⟩
  rcases rawEdge with xqEdge | qzEdge
  · change decide (exists face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (xqEdge = faceXQEdge P face 0 ∨
            xqEdge = faceXQEdge P face 1) = true) = true at member
    obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
    let starFace : XStarFace P x := ⟨face, hface⟩
    rcases of_decide_eq_true huse with hzero | hone
    · have hedge :
          (⟨Sum.inl xqEdge, member⟩ : XStarEdge P x) =
            xStarFaceXQEdge P x starFace 0 := by
        apply Subtype.ext
        exact congrArg Sum.inl hzero
      rw [hedge]
      exact rxCxH1_xqTerminal_equation P A3 x S word copy starFace 0
        segment hterminal
    · have hedge :
          (⟨Sum.inl xqEdge, member⟩ : XStarEdge P x) =
            xStarFaceXQEdge P x starFace 1 := by
        apply Subtype.ext
        exact congrArg Sum.inl hone
      rw [hedge]
      exact rxCxH1_xqTerminal_equation P A3 x S word copy starFace 1
        segment hterminal
  · change decide (exists face : P.Face,
        xStarFaceMember P x face = true ∧
          decide (qzEdge = faceQZEdge P face 0 ∨
            qzEdge = faceQZEdge P face 1) = true) = true at member
    obtain ⟨face, hface, huse⟩ := of_decide_eq_true member
    let starFace : XStarFace P x := ⟨face, hface⟩
    rcases of_decide_eq_true huse with hzero | hone
    · have hedge :
          (⟨Sum.inr qzEdge, member⟩ : XStarEdge P x) =
            xStarFaceQZEdge P x starFace 0 := by
        apply Subtype.ext
        exact congrArg Sum.inr hzero
      rw [hedge]
      exact rxCxH1_qzTerminal_equation P A3 R x S word hword copy
        starFace 0 segment hterminal
    · have hedge :
          (⟨Sum.inr qzEdge, member⟩ : XStarEdge P x) =
            xStarFaceQZEdge P x starFace 1 := by
        apply Subtype.ext
        exact congrArg Sum.inr hone
      rw [hedge]
      exact rxCxH1_qzTerminal_equation P A3 R x S word hword copy
        starFace 1 segment hterminal
private theorem rxCxH1_subdivisionEdge_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (edge : SubdivisionEdge P x S) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S edge) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S edge) =
      word (Sum.inl (copy, edge)) := by
  rcases edge with original | horizontal | vertical
  · rcases original with ⟨edge, segment⟩
    by_cases hterminal : segment.1 + 1 = S.half
    · exact rxCxH1_starEdgeTerminal_equation
        P A3 R x S word hword copy edge segment hterminal
    · exact rxCxH1_segmentInterior_equation P A3 x S word copy
        edge segment (by have := segment.2; omega)
  · rcases horizontal with ⟨face, segment, row⟩
    have hrow : row.1 + 1 < S.half := by
      have := row.2
      omega
    have hrowZero : row.1 + 1 ≠ 0 := by omega
    have hrowLast : row.1 + 1 ≠ S.half := by omega
    have hhorizontal := rxCxH1_horizontalLower_equation P A3 x S word hword copy face segment
        (row.1 + 1) hrow
    simp [subdivisionHorizontalEdge, hrowZero, hrowLast] at hhorizontal
    exact hhorizontal
  · rcases vertical with ⟨face, column, segment⟩
    let horizontal : Fin (S.half + 1) := ⟨column.1 + 1, by
      have := column.2
      have := S.half_pos
      omega⟩
    have hhorizontalZero : horizontal.1 ≠ 0 := by
      dsimp only [horizontal]
      omega
    have hhorizontalLast : horizontal.1 ≠ S.half := by
      dsimp only [horizontal]
      have := column.2
      omega
    by_cases hterminal : segment.1 + 1 = S.half
    · let terminal : Fin S.half := ⟨S.half - 1, by
        have := S.half_pos
        omega⟩
      have hsegment : segment = terminal := by
        apply Fin.ext
        dsimp only [terminal]
        omega
      rw [hsegment]
      have hvertical := rxCxH1_verticalTerminalInterior_equation
          P A3 x S word hword copy face column.1 (by
            have := column.2
            omega)
      simp [subdivisionVerticalEdge, horizontal, hhorizontalZero,
        hhorizontalLast] at hvertical
      exact hvertical
    · have hvertical := rxCxH1_verticalNonterminal_equation P A3 x S word copy face
          horizontal segment (by have := segment.2; omega)
      simp [subdivisionVerticalEdge, horizontal, hhorizontalZero,
        hhorizontalLast] at hvertical
      exact hvertical
private theorem rxCxH1_glueDiscrepancy_edge_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (edge : SubdivisionBoundaryEdge P x S) :
    rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionBoundaryEdgeStart P x S edge) =
      rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionBoundaryEdgeEnd P x S edge) := by
  have hcopyZero := rxCxH1_subdivisionEdge_equation
    P A3 R x S word hword 0 edge.1
  have hcopyOne := rxCxH1_subdivisionEdge_equation
    P A3 R x S word hword 1 edge.1
  have hcopyZero' :
      rxCxH1_subdivisionPotential P A3 x S word 0
          (subdivisionBoundaryEdgeStart P x S edge).1 +
        rxCxH1_subdivisionPotential P A3 x S word 0
          (subdivisionBoundaryEdgeEnd P x S edge).1 =
        word (Sum.inl (0, edge.1)) := by
    simpa using hcopyZero
  have hcopyOne' :
      rxCxH1_subdivisionPotential P A3 x S word 1
          (subdivisionBoundaryEdgeStart P x S edge).1 +
        rxCxH1_subdivisionPotential P A3 x S word 1
          (subdivisionBoundaryEdgeEnd P x S edge).1 =
        word (Sum.inl (1, edge.1)) := by
    simpa using hcopyOne
  have hrectangle := rxCxH1_rectangle_sum_eq_zero
    P x S word hword edge
  simp only [doubleCylinderRectangleBoundaryEdge_zero,
    doubleCylinderRectangleBoundaryEdge_one_zero,
    doubleCylinderRectangleBoundaryEdge_one_one] at hrectangle
  rw [← hcopyZero', ← hcopyOne'] at hrectangle
  have hsum :
      rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeStart P x S edge) +
        rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeEnd P x S edge) = 0 := by
    unfold rxCxH1_glueDiscrepancy
    rw [show
      (rxCxH1_subdivisionPotential P A3 x S word 0
            (subdivisionBoundaryEdgeStart P x S edge).1 +
          rxCxH1_subdivisionPotential P A3 x S word 1
            (subdivisionBoundaryEdgeStart P x S edge).1 +
          word (Sum.inr (subdivisionBoundaryEdgeStart P x S edge))) +
        (rxCxH1_subdivisionPotential P A3 x S word 0
            (subdivisionBoundaryEdgeEnd P x S edge).1 +
          rxCxH1_subdivisionPotential P A3 x S word 1
            (subdivisionBoundaryEdgeEnd P x S edge).1 +
          word (Sum.inr (subdivisionBoundaryEdgeEnd P x S edge))) =
        (rxCxH1_subdivisionPotential P A3 x S word 0
            (subdivisionBoundaryEdgeStart P x S edge).1 +
          rxCxH1_subdivisionPotential P A3 x S word 0
            (subdivisionBoundaryEdgeEnd P x S edge).1) +
        (rxCxH1_subdivisionPotential P A3 x S word 1
            (subdivisionBoundaryEdgeStart P x S edge).1 +
          rxCxH1_subdivisionPotential P A3 x S word 1
            (subdivisionBoundaryEdgeEnd P x S edge).1) +
        word (Sum.inr (subdivisionBoundaryEdgeStart P x S edge)) +
          word (Sum.inr (subdivisionBoundaryEdgeEnd P x S edge)) by abel]
    exact hrectangle
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg, neg_eq_self] using hsum
private theorem rxCxH1_boundarySegment_next
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (segment : Nat)
    (hnext : segment + 1 < S.half) :
    subdivisionBoundaryEdgeEnd P x S
        (subdivisionOriginalBoundaryEdge P x S edge
          ⟨segment, by omega⟩) =
      subdivisionBoundaryEdgeStart P x S
        (subdivisionOriginalBoundaryEdge P x S edge
          ⟨segment + 1, by omega⟩) := by
  apply Subtype.ext
  rw [subdivisionBoundaryEdgeEnd_value,
    subdivisionBoundaryEdgeStart_value]
  simp [subdivisionOriginalBoundaryEdge, subdivisionEdgeStart,
    subdivisionEdgeEnd, subdivisionSegmentStart, subdivisionSegmentEnd,
    hnext.ne]
private theorem rxCxH1_boundarySegment_first
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) :
    subdivisionBoundaryEdgeStart P x S
        (subdivisionOriginalBoundaryEdge P x S edge
          ⟨0, S.half_pos⟩) =
      subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeStart P x edge) := by
  apply Subtype.ext
  rw [subdivisionBoundaryEdgeStart_value]
  simp [subdivisionOriginalBoundaryEdge, subdivisionOriginalBoundaryVertex,
    subdivisionEdgeStart, subdivisionSegmentStart]
private theorem rxCxH1_boundarySegment_last
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) :
    subdivisionBoundaryEdgeEnd P x S
        (subdivisionOriginalBoundaryEdge P x S edge
          ⟨S.half - 1, by have := S.half_pos; omega⟩) =
      subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x edge) := by
  apply Subtype.ext
  rw [subdivisionBoundaryEdgeEnd_value]
  simp [subdivisionOriginalBoundaryEdge, subdivisionOriginalBoundaryVertex,
    subdivisionEdgeEnd, subdivisionSegmentEnd]
  exact Nat.sub_add_cancel S.half_pos
private theorem rxCxH1_glueDiscrepancy_oldEdge_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (edge : XStarBoundaryEdge P x) :
    rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionOriginalBoundaryVertex P x S
          (xBoundaryEdgeStart P x edge)) =
      rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionOriginalBoundaryVertex P x S
          (xBoundaryEdgeEnd P x edge)) := by
  let segmentEdge : Fin S.half → SubdivisionBoundaryEdge P x S :=
    subdivisionOriginalBoundaryEdge P x S edge
  have hprefix : ∀ (segment : Nat) (hsegment : segment < S.half),
      rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeStart P x S
            (segmentEdge ⟨0, S.half_pos⟩)) =
        rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeEnd P x S
            (segmentEdge ⟨segment, hsegment⟩)) := by
    intro segment hsegment
    induction segment with
    | zero =>
        exact rxCxH1_glueDiscrepancy_edge_eq P A3 R x S word hword
          (segmentEdge ⟨0, hsegment⟩)
    | succ segment ih =>
        have hprevious : segment < S.half := by omega
        calc
          rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeStart P x S
                  (segmentEdge ⟨0, S.half_pos⟩)) =
              rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeEnd P x S
                  (segmentEdge ⟨segment, hprevious⟩)) :=
            ih hprevious
          _ = rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeStart P x S
                  (segmentEdge ⟨segment + 1, hsegment⟩)) := by
            exact congrArg (rxCxH1_glueDiscrepancy P A3 x S word)
              (rxCxH1_boundarySegment_next P x S edge segment hsegment)
          _ = rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeEnd P x S
                  (segmentEdge ⟨segment + 1, hsegment⟩)) :=
            rxCxH1_glueDiscrepancy_edge_eq P A3 R x S word hword
              (segmentEdge ⟨segment + 1, hsegment⟩)
  have hlast := hprefix (S.half - 1) (by
    have := S.half_pos
    omega)
  rw [rxCxH1_boundarySegment_first,
    rxCxH1_boundarySegment_last] at hlast
  exact hlast
private theorem rxCxH1_oldBoundaryDiscrepancy_coboundary_eq_zero
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0) :
    wordLinearMapTranspose
        (graphBoundary (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x))
        (rxCxH1_oldBoundaryDiscrepancy P A3 x S word) = 0 := by
  ext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  change
    rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionOriginalBoundaryVertex P x S
            (xBoundaryEdgeStart P x edge)) +
        rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionOriginalBoundaryVertex P x S
            (xBoundaryEdgeEnd P x edge)) = 0
  rw [rxCxH1_glueDiscrepancy_oldEdge_eq P A3 R x S word hword edge]
  exact ZModModule.add_self _
private theorem rxCxH1_glueDiscrepancy_original_eq_offset
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (vertex : XStarBoundaryVertex P x) :
    rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionOriginalBoundaryVertex P x S vertex) =
      rxCxH1_glueOffset P A3 x S word := by
  let A := A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  have hconstant := word_eq_root_of_graphCoboundary_eq_zero
    (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
    (A.xBoundaryRoot x) (A.xBoundaryPath x)
    (rxCxH1_oldBoundaryDiscrepancy P A3 x S word)
    (rxCxH1_oldBoundaryDiscrepancy_coboundary_eq_zero
      P A3 R x S word hword) vertex
  simpa [rxCxH1_oldBoundaryDiscrepancy, rxCxH1_glueOffset, A] using
    hconstant
private theorem rxCxH1_glueDiscrepancy_segmentEnd_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (edge : XStarBoundaryEdge P x) (selected : Fin S.half) :
    rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionOriginalBoundaryVertex P x S
          (xBoundaryEdgeStart P x edge)) =
      rxCxH1_glueDiscrepancy P A3 x S word
        (subdivisionBoundaryEdgeEnd P x S
          (subdivisionOriginalBoundaryEdge P x S edge selected)) := by
  let segmentEdge : Fin S.half → SubdivisionBoundaryEdge P x S :=
    subdivisionOriginalBoundaryEdge P x S edge
  have hprefix : ∀ (segment : Nat) (hsegment : segment < S.half),
      rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeStart P x S
            (segmentEdge ⟨0, S.half_pos⟩)) =
        rxCxH1_glueDiscrepancy P A3 x S word
          (subdivisionBoundaryEdgeEnd P x S
            (segmentEdge ⟨segment, hsegment⟩)) := by
    intro segment hsegment
    induction segment with
    | zero =>
        exact rxCxH1_glueDiscrepancy_edge_eq P A3 R x S word hword
          (segmentEdge ⟨0, hsegment⟩)
    | succ segment ih =>
        have hprevious : segment < S.half := by omega
        calc
          rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeStart P x S
                  (segmentEdge ⟨0, S.half_pos⟩)) =
              rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeEnd P x S
                  (segmentEdge ⟨segment, hprevious⟩)) :=
            ih hprevious
          _ = rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeStart P x S
                  (segmentEdge ⟨segment + 1, hsegment⟩)) := by
            exact congrArg (rxCxH1_glueDiscrepancy P A3 x S word)
              (rxCxH1_boundarySegment_next P x S edge segment hsegment)
          _ = rxCxH1_glueDiscrepancy P A3 x S word
                (subdivisionBoundaryEdgeEnd P x S
                  (segmentEdge ⟨segment + 1, hsegment⟩)) :=
            rxCxH1_glueDiscrepancy_edge_eq P A3 R x S word hword
              (segmentEdge ⟨segment + 1, hsegment⟩)
  have hselected := hprefix selected.1 selected.2
  rw [rxCxH1_boundarySegment_first] at hselected
  exact hselected
private theorem rxCxH1_boundaryInterior_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (interior : Fin (S.half - 1)) :
    subdivisionBoundaryEdgeEnd P x S
        (subdivisionOriginalBoundaryEdge P x S edge
          ⟨interior.1, by have := interior.2; omega⟩) =
      (⟨Sum.inr
          (Sum.inl (xStarBoundaryEdgeToStar P x edge, interior)), by
        simpa [subdivisionBoundaryVertexMember, xStarBoundaryEdgeToStar] using edge.2⟩ :
        SubdivisionBoundaryVertex P x S) := by
  apply Subtype.ext
  rw [subdivisionBoundaryEdgeEnd_value]
  have hnot : interior.1 + 1 ≠ S.half := by
    have := interior.2
    omega
  simp [subdivisionOriginalBoundaryEdge, subdivisionEdgeEnd,
    subdivisionSegmentEnd, hnot]
private theorem rxCxH1_glueDiscrepancy_eq_offset
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (vertex : SubdivisionBoundaryVertex P x S) :
    rxCxH1_glueDiscrepancy P A3 x S word vertex =
      rxCxH1_glueOffset P A3 x S word := by
  rcases vertex with ⟨vertex, hboundary⟩
  rcases vertex with original | interior
  · let boundaryVertex : XStarBoundaryVertex P x :=
      ⟨original.1, by
        simpa [subdivisionBoundaryVertexMember] using hboundary⟩
    simpa [subdivisionOriginalBoundaryVertex, xStarBoundaryVertexToStar,
      boundaryVertex] using
      rxCxH1_glueDiscrepancy_original_eq_offset
        P A3 R x S word hword boundaryVertex
  · rcases interior with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨starEdge, interior⟩
      let boundaryEdge : XStarBoundaryEdge P x :=
        ⟨starEdge.1, by
          simpa [subdivisionBoundaryVertexMember] using hboundary⟩
      let selected : Fin S.half := ⟨interior.1, by
        have := interior.2
        omega⟩
      have hprefix := rxCxH1_glueDiscrepancy_segmentEnd_eq
        P A3 R x S word hword boundaryEdge selected
      have hinterior := rxCxH1_boundaryInterior_end
        P x S boundaryEdge interior
      have hendpoint :
          subdivisionBoundaryEdgeEnd P x S
              (subdivisionOriginalBoundaryEdge P x S boundaryEdge selected) =
            (⟨Sum.inr (Sum.inl (starEdge, interior)), hboundary⟩ :
              SubdivisionBoundaryVertex P x S) := by
        simpa [selected, boundaryEdge, xStarBoundaryEdgeToStar] using hinterior
      have hstart := rxCxH1_glueDiscrepancy_original_eq_offset
        P A3 R x S word hword (xBoundaryEdgeStart P x boundaryEdge)
      rw [hendpoint] at hprefix
      exact hprefix.symm.trans hstart
    · simp [subdivisionBoundaryVertexMember] at hboundary
private theorem rxCxH1_verticalGlue_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (vertex : SubdivisionBoundaryVertex P x S) :
    rxCxH1_doubleCylinderPotential P A3 x S word
        (tannerDoubleCylinderEdgeStart P x S (Sum.inr vertex)) +
      rxCxH1_doubleCylinderPotential P A3 x S word
        (tannerDoubleCylinderEdgeEnd P x S (Sum.inr vertex)) =
      word (Sum.inr vertex) := by
  have hdiscrepancy := rxCxH1_glueDiscrepancy_eq_offset
    P A3 R x S word hword vertex
  simp only [tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd,
    rxCxH1_doubleCylinderPotential, rxTwoElim_zero, rxTwoElim_one]
  simp only [add_zero]
  rw [← hdiscrepancy]
  unfold rxCxH1_glueDiscrepancy
  rw [show
    rxCxH1_subdivisionPotential P A3 x S word 0 vertex.1 +
        (rxCxH1_subdivisionPotential P A3 x S word 1 vertex.1 +
          (rxCxH1_subdivisionPotential P A3 x S word 0 vertex.1 +
            rxCxH1_subdivisionPotential P A3 x S word 1 vertex.1 +
              word (Sum.inr vertex))) =
      (rxCxH1_subdivisionPotential P A3 x S word 0 vertex.1 +
          rxCxH1_subdivisionPotential P A3 x S word 0 vertex.1) +
        (rxCxH1_subdivisionPotential P A3 x S word 1 vertex.1 +
          rxCxH1_subdivisionPotential P A3 x S word 1 vertex.1) +
        word (Sum.inr vertex) by abel]
  rw [ZModModule.add_self, ZModModule.add_self]
  simp
private theorem rxCxH1_doubleCylinderEdge_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (edge : DoubleCylinderEdge P x S) :
    rxCxH1_doubleCylinderPotential P A3 x S word
        (tannerDoubleCylinderEdgeStart P x S edge) +
      rxCxH1_doubleCylinderPotential P A3 x S word
        (tannerDoubleCylinderEdgeEnd P x S edge) =
      word edge := by
  rcases edge with copyEdge | vertex
  · rcases copyEdge with ⟨copy, edge⟩
    have hedge := rxCxH1_subdivisionEdge_equation
      P A3 R x S word hword copy edge
    fin_cases copy
    · simpa [rxCxH1_doubleCylinderPotential, rxTwoElim,
        tannerDoubleCylinderEdgeStart, tannerDoubleCylinderEdgeEnd] using
        hedge
    · change
        (rxCxH1_subdivisionPotential P A3 x S word 1
              (subdivisionEdgeStart P x S edge) +
            rxCxH1_glueOffset P A3 x S word) +
          (rxCxH1_subdivisionPotential P A3 x S word 1
              (subdivisionEdgeEnd P x S edge) +
            rxCxH1_glueOffset P A3 x S word) =
          word (Sum.inl (1, edge))
      rw [show
        (rxCxH1_subdivisionPotential P A3 x S word 1
              (subdivisionEdgeStart P x S edge) +
            rxCxH1_glueOffset P A3 x S word) +
          (rxCxH1_subdivisionPotential P A3 x S word 1
              (subdivisionEdgeEnd P x S edge) +
            rxCxH1_glueOffset P A3 x S word) =
          (rxCxH1_subdivisionPotential P A3 x S word 1
                (subdivisionEdgeStart P x S edge) +
              rxCxH1_subdivisionPotential P A3 x S word 1
                (subdivisionEdgeEnd P x S edge)) +
            (rxCxH1_glueOffset P A3 x S word +
              rxCxH1_glueOffset P A3 x S word) by abel]
      rw [ZModModule.add_self, add_zero]
      exact hedge
  · exact rxCxH1_verticalGlue_equation P A3 R x S word hword vertex
private theorem rxCxH1_doubleCylinderPotential_coboundary_eq
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0) :
    wordLinearMapTranspose (rxCx P x S).boundary1
        (rxCxH1_doubleCylinderPotential P A3 x S word) = word := by
  classical
  change wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
      (rxCxH1_doubleCylinderPotential P A3 x S word) = word
  rw [← doubleCylinderGraphBoundary_eq_boundary1]
  change wordLinearMapTranspose
      (graphBoundary (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S))
      (rxCxH1_doubleCylinderPotential P A3 x S word) = word
  ext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  exact rxCxH1_doubleCylinderEdge_equation P A3 R x S word hword edge
private theorem rxCxH1Coordinate_bijective_of_exact
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (hexact : (rxCx P x S).firstCoboundaryCheckCode.carrier =
      (rxCx P x S).middleCocycleCode.carrier) :
    Function.Bijective (rxCxH1Coordinate P x S) := by
  constructor
  · intro first second _
    refine Submodule.Quotient.induction_on _ first ?_
    intro firstWord
    refine Submodule.Quotient.induction_on _ second ?_
    intro secondWord
    rw [Submodule.Quotient.eq]
    change (firstWord - secondWord).1 ∈
      (rxCx P x S).firstCoboundaryCheckCode.carrier
    rw [hexact]
    exact (rxCx P x S).middleCocycleCode.carrier.sub_mem
      firstWord.2 secondWord.2
  · intro value
    exact ⟨0, Subsingleton.elim _ value⟩
private theorem rxCxH1_firstCoboundary_eq_middleCocycle
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale) :
    (rxCx P x S).firstCoboundaryCheckCode.carrier =
      (rxCx P x S).middleCocycleCode.carrier := by
  apply le_antisymm
  · exact (rxCx P x S).firstCoboundaryCheckCode_le_middleCocycleCode
  · intro word hword
    apply ((rxCx P x S).mem_firstCoboundaryCheckCode_iff word).2
    refine ⟨rxCxH1_doubleCylinderPotential P A3 x S word, ?_⟩
    exact rxCxH1_doubleCylinderPotential_coboundary_eq
      P A3 R x S word
        (((rxCx P x S).mem_middleCocycleCode_iff word).1 hword)
open BDL26BoundedValence
end BDL26RXLocalReplacement
end Coding
end QEC
end

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale) :
    Function.Bijective (rxCxH1Coordinate P x S) :=
  rxCxH1Coordinate_bijective_of_exact P x S
    (rxCxH1_firstCoboundary_eq_middleCocycle P A3 R x S)
end QEC.Coding.BDL26RXLocalReplacement
