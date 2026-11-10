-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCxH1_qzTerminal_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:42:59.700205+00:00
-- url     : https://prove2.me/submissions/02df2820-9788-401b-9984-10e038727c09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
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
private theorem rxCxH1_topRightLeft_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x) :
    let terminal : Fin S.half := ⟨S.half - 1, by
      have := S.half_pos
      omega⟩
    let horizontal : Fin (S.half + 1) := ⟨S.half - 1, by omega⟩
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeStart P x S
          (subdivisionVerticalEdge P x S face horizontal terminal)) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionEdgeEnd P x S
          (subdivisionVerticalEdge P x S face horizontal terminal)) =
      word (Sum.inl (copy,
        subdivisionVerticalEdge P x S face horizontal terminal)) := by
  dsimp only
  let terminal : Fin S.half := ⟨S.half - 1, by
    have := S.half_pos
    omega⟩
  by_cases hone : S.half = 1
  · have horizontalZero :
        (⟨S.half - 1, by omega⟩ : Fin (S.half + 1)) = 0 := by
      apply Fin.ext
      change S.half - 1 = 0
      omega
    rw [horizontalZero]
    simpa [subdivisionVerticalEdge, subdivisionEdgeStart, subdivisionEdgeEnd] using
      rxCxH1_xqTerminal_equation P A3 x S word copy face 1 terminal
        (by dsimp only [terminal]; omega)
  · let column := S.half - 2
    have hcolumn : column + 1 < S.half := by
      dsimp only [column]
      have := S.half_pos
      omega
    have horizontalEq :
        (⟨column + 1, by omega⟩ : Fin (S.half + 1)) =
          ⟨S.half - 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [column]
      omega
    rw [← horizontalEq]
    exact rxCxH1_verticalTerminalInterior_equation
      P A3 x S word hword copy face column hcolumn
private theorem rxCxH1_oldZOwner_edge_cases
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X)
    (face : XStarFace P x) :
    let vertex : XStarBoundaryVertex P x :=
      ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
    let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
    owner.1.1.1 = xStarFaceQZEdge P x face 0 ∨
      owner.1.1.1 = xStarFaceQZEdge P x face 1 := by
  dsimp only
  let vertex : XStarBoundaryVertex P x :=
    ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
  let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
  generalize howned : owner.1.1 = selected
  rcases selected with ⟨rawEdge, edgeMember⟩
  rcases rawEdge with impossible | qzEdge
  · simp [xStarBoundaryEdgeMember] at edgeMember
  · have starMember : xStarEdgeMember P x (Sum.inr qzEdge) = true :=
      edgeMember
    change decide (exists candidate : P.Face,
      xStarFaceMember P x candidate = true ∧
        decide (qzEdge = faceQZEdge P candidate 0 ∨
          qzEdge = faceQZEdge P candidate 1) = true) = true at starMember
    obtain ⟨candidate, hcandidate, hedge⟩ := of_decide_eq_true starMember
    have hcandidateX : P.faceX candidate = x := by
      simpa [xStarFaceMember] using hcandidate
    have hendpoint := owner.2
    rw [howned] at hendpoint
    have hqzZ : qzEdge.1.2 = P.faceZ face.1 := by
      have hcases : owner.1.2 = 0 ∨ owner.1.2 = 1 :=
        rxTwoElim (motive := fun endpoint => endpoint = 0 ∨ endpoint = 1)
          (Or.inl rfl) (Or.inr rfl) owner.1.2
      rcases hcases with hzero | hone
      · rw [hzero] at hendpoint
        rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
        simp only [xBoundaryEdgeStart] at hendpoint
        have hraw := congrArg Subtype.val hendpoint
        dsimp only [vertex] at hraw
        change Vertex.q qzEdge.1.1 = Vertex.z (P.faceZ face.1) at hraw
        cases hraw
      · rw [hone] at hendpoint
        rw [BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
        simp only [xBoundaryEdgeEnd] at hendpoint
        have hraw := congrArg Subtype.val hendpoint
        dsimp only [vertex] at hraw
        exact Vertex.z.inj hraw
    have hcandidateZ : P.faceZ candidate = P.faceZ face.1 := by
      rcases of_decide_eq_true hedge with hedge | hedge
      · have hz := congrArg (fun edge : QZEdge P => edge.1.2) hedge
        exact hz.symm.trans hqzZ
      · have hz := congrArg (fun edge : QZEdge P => edge.1.2) hedge
        exact hz.symm.trans hqzZ
    have hfaceX : P.faceX face.1 = x := by
      simpa [xStarFaceMember] using face.2
    have hcandidateEq : candidate = face.1 := by
      apply R.faceXZ_injective
      exact Prod.ext (hcandidateX.trans hfaceX.symm) hcandidateZ
    subst candidate
    rcases of_decide_eq_true hedge with hedge | hedge
    · left
      exact congrArg Sum.inr hedge
    · right
      exact congrArg Sum.inr hedge
private theorem rxCxH1_oldZOwner_endpoint_one
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (face : XStarFace P x) :
    let vertex : XStarBoundaryVertex P x :=
      ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
    (A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex).1.2 = 1 := by
  dsimp only
  let vertex : XStarBoundaryVertex P x :=
    ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
  let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
  have hendpoint := owner.2
  have hcases : owner.1.2 = 0 ∨ owner.1.2 = 1 :=
    rxTwoElim (motive := fun endpoint => endpoint = 0 ∨ endpoint = 1)
      (Or.inl rfl) (Or.inr rfl) owner.1.2
  rcases hcases with hzero | hone
  · rw [hzero] at hendpoint
    rw [BDL26TannerLocalRegularity.edgeEndpoint_zero] at hendpoint
    rcases howned : owner.1.1 with ⟨rawEdge, edgeMember⟩
    rcases rawEdge with impossible | qzEdge
    · simp [xStarBoundaryEdgeMember] at edgeMember
    · rw [howned] at hendpoint
      simp only [xBoundaryEdgeStart] at hendpoint
      have hraw := congrArg Subtype.val hendpoint
      dsimp only [vertex] at hraw
      change Vertex.q qzEdge.1.1 = Vertex.z (P.faceZ face.1) at hraw
      cases hraw
  · exact hone
private theorem rxCxH1_segmentTerminal_equation_of_endpoint
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (edge : XStarEdge P x)
    (hendpoint :
      rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeEnd P x edge) =
        rxCxH1_oldVertexPotential P A3 x S word copy
            (xStarEdgeStart P x edge) +
          rxCxH1_segmentPrefix P x S word copy edge S.half
            (le_refl S.half))
    (segment : Fin S.half) (hterminal : segment.1 + 1 = S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S edge segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S edge segment) =
      word (Sum.inl (copy, Sum.inl (edge, segment))) := by
  rcases segment with ⟨segment, hsegment⟩
  rcases segment with _ | segment
  · change 1 = S.half at hterminal
    have hstart : subdivisionSegmentStart P x S edge ⟨0, hsegment⟩ =
        Sum.inl (xStarEdgeStart P x edge) := by
      simp [subdivisionSegmentStart]
    have hend : subdivisionSegmentEnd P x S edge ⟨0, hsegment⟩ =
        Sum.inl (xStarEdgeEnd P x edge) := by
      simp [subdivisionSegmentEnd, hterminal]
    rw [hstart, hend]
    simp only [rxCxH1_subdivisionPotential]
    rw [hendpoint]
    have hprefixFull :
        rxCxH1_segmentPrefix P x S word copy edge S.half
            (le_refl S.half) =
          rxCxH1_segmentPrefix P x S word copy edge 1 (by omega) := by
      congr 1
      exact hterminal.symm
    rw [hprefixFull, rxCxH1_segmentPrefix]
    simp only [rxCxH1_segmentPrefix, zero_add]
    simpa using rxCxH1_cancel_successive
      (rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x edge)) 0
      (word (Sum.inl (copy, Sum.inl (edge, ⟨0, hsegment⟩))))
  · change segment + 2 = S.half at hterminal
    have hnotzero : segment + 1 ≠ 0 := by omega
    let interior : Fin (S.half - 1) := ⟨segment, by omega⟩
    have hstart : subdivisionSegmentStart P x S edge
        ⟨segment + 1, hsegment⟩ =
        Sum.inr (Sum.inl (edge, interior)) := by
      simp [subdivisionSegmentStart, hnotzero, interior]
    have hend : subdivisionSegmentEnd P x S edge
        ⟨segment + 1, hsegment⟩ =
        Sum.inl (xStarEdgeEnd P x edge) := by
      simp [subdivisionSegmentEnd, hterminal]
    rw [hstart, hend]
    simp only [rxCxH1_subdivisionPotential]
    rw [hendpoint]
    have hprefixFull :
        rxCxH1_segmentPrefix P x S word copy edge S.half
            (le_refl S.half) =
          rxCxH1_segmentPrefix P x S word copy edge (segment + 2)
            (by omega) := by
      congr 1
      exact hterminal.symm
    rw [hprefixFull]
    rw (occs := .pos [2]) [rxCxH1_segmentPrefix]
    dsimp only [interior]
    exact rxCxH1_cancel_successive
      (rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x edge))
      (rxCxH1_segmentPrefix P x S word copy edge (segment + 1) (by omega))
      (word (Sum.inl (copy, Sum.inl (edge, ⟨segment + 1, hsegment⟩))))
private theorem rxCxH1_oldZOwner_endpointPotential
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) :
    let vertex : XStarBoundaryVertex P x :=
      ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
    let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
    rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeEnd P x (xStarBoundaryEdgeToStar P x owner.1.1)) =
      rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeStart P x (xStarBoundaryEdgeToStar P x owner.1.1)) +
        rxCxH1_segmentPrefix P x S word copy
          (xStarBoundaryEdgeToStar P x owner.1.1) S.half (le_refl S.half) := by
  dsimp only
  let vertex : XStarBoundaryVertex P x :=
    ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
  let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
  change rxCxH1_oldVertexPotential P A3 x S word copy
      (xStarEdgeEnd P x (xStarBoundaryEdgeToStar P x owner.1.1)) =
    rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeStart P x (xStarBoundaryEdgeToStar P x owner.1.1)) +
      rxCxH1_segmentPrefix P x S word copy
        (xStarBoundaryEdgeToStar P x owner.1.1) S.half (le_refl S.half)
  have hone : owner.1.2 = 1 :=
    rxCxH1_oldZOwner_endpoint_one P A3 x face
  have hendpoint := owner.2
  rw [hone, BDL26TannerLocalRegularity.edgeEndpoint_one] at hendpoint
  generalize howned : owner.1.1 = selected
  rcases selected with ⟨rawEdge, edgeMember⟩
  rcases rawEdge with impossible | qzEdge
  · simp [xStarBoundaryEdgeMember] at edgeMember
  · rw [howned] at hendpoint
    simp only [xBoundaryEdgeEnd] at hendpoint
    let starEdge : XStarEdge P x := ⟨Sum.inr qzEdge, edgeMember⟩
    have hend : xStarEdgeEnd P x starEdge = xStarFaceZVertex P x face := by
      apply Subtype.ext
      have hraw := congrArg Subtype.val hendpoint
      dsimp only [vertex] at hraw
      exact hraw
    change rxCxH1_oldVertexPotential P A3 x S word copy
        (xStarEdgeEnd P x starEdge) =
      rxCxH1_oldVertexPotential P A3 x S word copy
          (xStarEdgeStart P x starEdge) +
        rxCxH1_segmentPrefix P x S word copy starEdge S.half
          (le_refl S.half)
    rw [hend]
    simp only [xStarFaceZVertex, xStarEdgeStart]
    simp only [rxCxH1_oldVertexPotential]
    change rxCxH1_oldZOwnerPotential P x S word copy owner.1.1 = _
    rw [howned]
    simp only [rxCxH1_oldZOwnerPotential]
    rfl
private theorem rxCxH1_oldZOwner_terminal_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (segment : Fin S.half)
    (hterminal : segment.1 + 1 = S.half) :
    let vertex : XStarBoundaryVertex P x :=
      ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
    let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
    let edge := xStarBoundaryEdgeToStar P x owner.1.1
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S edge segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S edge segment) =
      word (Sum.inl (copy, Sum.inl (edge, segment))) := by
  dsimp only
  exact rxCxH1_segmentTerminal_equation_of_endpoint P A3 x S word copy
    _ (rxCxH1_oldZOwner_endpointPotential P A3 x S word copy face)
    segment hterminal
private theorem rxCxH1_qzTerminal_equation_of_owner
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S)) (copy : Two)
    (face : XStarFace P x) (corner : Two) (segment : Fin S.half)
    (hterminal : segment.1 + 1 = S.half)
    (howner :
      let vertex : XStarBoundaryVertex P x :=
        ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
      let owner :=
        A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
      owner.1.1.1 = xStarFaceQZEdge P x face corner) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceQZEdge P x face corner) segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceQZEdge P x face corner) segment) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge P x face corner, segment))) := by
  let vertex : XStarBoundaryVertex P x :=
    ⟨Vertex.z (P.faceZ face.1), (xStarFaceZVertex P x face).2⟩
  let owner := A3.toTannerSquareAdmissibleV2.xBoundaryIncidentEdge x vertex
  have hedge :
      xStarBoundaryEdgeToStar P x owner.1.1 =
        xStarFaceQZEdge P x face corner := by
    apply Subtype.ext
    simpa [owner, vertex, xStarBoundaryEdgeToStar] using howner
  have hselected := rxCxH1_oldZOwner_terminal_equation
    P A3 x S word copy face segment hterminal
  dsimp only at hselected
  rw [hedge] at hselected
  exact hselected
private theorem rxCxH1_qzOne_terminal_of_qzZero
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x)
    (hzero :
      let terminal : Fin S.half := ⟨S.half - 1, by
        have := S.half_pos
        omega⟩
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentStart P x S
            (xStarFaceQZEdge P x face 0) terminal) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentEnd P x S
            (xStarFaceQZEdge P x face 0) terminal) =
        word (Sum.inl (copy, Sum.inl
          (xStarFaceQZEdge P x face 0, terminal)))) :
    let terminal : Fin S.half := ⟨S.half - 1, by
      have := S.half_pos
      omega⟩
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceQZEdge P x face 1) terminal) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceQZEdge P x face 1) terminal) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge P x face 1, terminal))) := by
  dsimp only
  let terminal : Fin S.half := ⟨S.half - 1, by
    have := S.half_pos
    omega⟩
  let cell : SubdivisionFace P x S := (face, terminal, terminal)
  let potential : Word Field (SubdivisionVertex P x S) :=
    rxCxH1_subdivisionPotential P A3 x S word copy
  have htopEdge :
      subdivisionFaceBoundaryEdge P x S cell (0, 1) =
        subdivisionHorizontalEdge P x S face terminal
          ⟨S.half, by omega⟩ := by
    rw [subdivisionFaceBoundaryEdge_zero_one]
    congr 1
    apply Fin.ext
    rw [finSuccGrid_val]
    dsimp only [cell, terminal]
    have := S.half_pos
    omega
  have hrightEdge :
      subdivisionFaceBoundaryEdge P x S cell (1, 1) =
        subdivisionVerticalEdge P x S face ⟨S.half, by omega⟩
          terminal := by
    rw [subdivisionFaceBoundaryEdge_one_one]
    congr 1
    apply Fin.ext
    rw [finSuccGrid_val]
    dsimp only [cell, terminal]
    have := S.half_pos
    omega
  have hhalf : S.half ≠ 0 := S.half_pos.ne'
  change potential
        (subdivisionEdgeStart P x S
          (Sum.inl (xStarFaceQZEdge P x face 1, terminal))) +
      potential
        (subdivisionEdgeEnd P x S
          (Sum.inl (xStarFaceQZEdge P x face 1, terminal))) =
      word (Sum.inl (copy,
        Sum.inl (xStarFaceQZEdge P x face 1, terminal)))
  have htopBoundary :
      subdivisionHorizontalEdge P x S face terminal
          ⟨S.half, by omega⟩ =
        Sum.inl (xStarFaceQZEdge P x face 1, terminal) := by
    simp [subdivisionHorizontalEdge, hhalf]
  rw [← htopBoundary, ← htopEdge]
  apply rxCxH1_smallSquare_curl_transport
    P x S word hword copy potential cell
  · change
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionHorizontalEdge P x S face terminal
              ⟨S.half - 1, by omega⟩)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionHorizontalEdge P x S face terminal
              ⟨S.half - 1, by omega⟩)) =
        word (Sum.inl (copy, subdivisionHorizontalEdge P x S face terminal
          ⟨S.half - 1, by omega⟩))
    exact rxCxH1_horizontalLower_equation P A3 x S word hword copy
      face terminal (S.half - 1) (by omega)
  · rw [hrightEdge]
    dsimp only [potential]
    simpa [subdivisionVerticalEdge, hhalf, subdivisionEdgeStart, subdivisionEdgeEnd] using hzero
  · change
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionVerticalEdge P x S face
              ⟨S.half - 1, by omega⟩ terminal)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionVerticalEdge P x S face
              ⟨S.half - 1, by omega⟩ terminal)) =
        word (Sum.inl (copy, subdivisionVerticalEdge P x S face
          ⟨S.half - 1, by omega⟩ terminal))
    exact rxCxH1_topRightLeft_equation
      P A3 x S word hword copy face
private theorem rxCxH1_qzZero_terminal_of_qzOne
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x)
    (hone :
      let terminal : Fin S.half := ⟨S.half - 1, by
        have := S.half_pos
        omega⟩
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentStart P x S
            (xStarFaceQZEdge P x face 1) terminal) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentEnd P x S
            (xStarFaceQZEdge P x face 1) terminal) =
        word (Sum.inl (copy, Sum.inl
          (xStarFaceQZEdge P x face 1, terminal)))) :
    let terminal : Fin S.half := ⟨S.half - 1, by
      have := S.half_pos
      omega⟩
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceQZEdge P x face 0) terminal) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceQZEdge P x face 0) terminal) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge P x face 0, terminal))) := by
  dsimp only
  let terminal : Fin S.half := ⟨S.half - 1, by
    have := S.half_pos
    omega⟩
  let cell : SubdivisionFace P x S := (face, terminal, terminal)
  let potential : Word Field (SubdivisionVertex P x S) :=
    rxCxH1_subdivisionPotential P A3 x S word copy
  have htopEdge :
      subdivisionFaceBoundaryEdge P x S cell (0, 1) =
        subdivisionHorizontalEdge P x S face terminal
          ⟨S.half, by omega⟩ := by
    rw [subdivisionFaceBoundaryEdge_zero_one]
    congr 1
    apply Fin.ext
    rw [finSuccGrid_val]
    dsimp only [cell, terminal]
    have := S.half_pos
    omega
  have hrightEdge :
      subdivisionFaceBoundaryEdge P x S cell (1, 1) =
        subdivisionVerticalEdge P x S face ⟨S.half, by omega⟩
          terminal := by
    rw [subdivisionFaceBoundaryEdge_one_one]
    congr 1
    apply Fin.ext
    rw [finSuccGrid_val]
    dsimp only [cell, terminal]
    have := S.half_pos
    omega
  have hhalf : S.half ≠ 0 := S.half_pos.ne'
  change potential
        (subdivisionEdgeStart P x S
          (Sum.inl (xStarFaceQZEdge P x face 0, terminal))) +
      potential
        (subdivisionEdgeEnd P x S
          (Sum.inl (xStarFaceQZEdge P x face 0, terminal))) =
      word (Sum.inl (copy,
        Sum.inl (xStarFaceQZEdge P x face 0, terminal)))
  have hrightBoundary :
      subdivisionVerticalEdge P x S face ⟨S.half, by omega⟩
          terminal =
        Sum.inl (xStarFaceQZEdge P x face 0, terminal) := by
    simp [subdivisionVerticalEdge, hhalf]
  rw [← hrightBoundary, ← hrightEdge]
  apply rxCxH1_smallSquare_curl_transport_right
    P x S word hword copy potential cell
  · change
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionHorizontalEdge P x S face terminal
              ⟨S.half - 1, by omega⟩)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionHorizontalEdge P x S face terminal
              ⟨S.half - 1, by omega⟩)) =
        word (Sum.inl (copy, subdivisionHorizontalEdge P x S face terminal
          ⟨S.half - 1, by omega⟩))
    exact rxCxH1_horizontalLower_equation P A3 x S word hword copy
      face terminal (S.half - 1) (by omega)
  · rw [htopEdge]
    dsimp only [potential]
    simpa [subdivisionHorizontalEdge, hhalf, subdivisionEdgeStart, subdivisionEdgeEnd] using hone
  · change
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeStart P x S
            (subdivisionVerticalEdge P x S face
              ⟨S.half - 1, by omega⟩ terminal)) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionEdgeEnd P x S
            (subdivisionVerticalEdge P x S face
              ⟨S.half - 1, by omega⟩ terminal)) =
        word (Sum.inl (copy, subdivisionVerticalEdge P x S face
          ⟨S.half - 1, by omega⟩ terminal))
    exact rxCxH1_topRightLeft_equation
      P A3 x S word hword copy face
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
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x) (corner : Two)
    (segment : Fin S.half) (hterminal : segment.1 + 1 = S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceQZEdge P x face corner) segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceQZEdge P x face corner) segment) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge P x face corner, segment))) := by
  let terminal : Fin S.half := ⟨S.half - 1, by
    have := S.half_pos
    omega⟩
  have hsegment : segment = terminal := by
    apply Fin.ext
    dsimp only [terminal]
    omega
  rw [hsegment]
  have hterminalLast : terminal.1 + 1 = S.half := by
    dsimp only [terminal]
    have := S.half_pos
    omega
  have hcases := rxCxH1_oldZOwner_edge_cases P A3 R x face
  rcases hcases with hzero | hone
  · have hselected := rxCxH1_qzTerminal_equation_of_owner
      P A3 x S word copy face 0 terminal hterminalLast hzero
    refine rxTwoElim (motive := fun corner : Two =>
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentStart P x S
            (xStarFaceQZEdge P x face corner) terminal) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentEnd P x S
            (xStarFaceQZEdge P x face corner) terminal) =
        word (Sum.inl (copy, Sum.inl
          (xStarFaceQZEdge P x face corner, terminal))))
      hselected
      (rxCxH1_qzOne_terminal_of_qzZero
        P A3 x S word hword copy face hselected)
      corner
  · have hselected := rxCxH1_qzTerminal_equation_of_owner
      P A3 x S word copy face 1 terminal hterminalLast hone
    refine rxTwoElim (motive := fun corner : Two =>
      rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentStart P x S
            (xStarFaceQZEdge P x face corner) terminal) +
        rxCxH1_subdivisionPotential P A3 x S word copy
          (subdivisionSegmentEnd P x S
            (xStarFaceQZEdge P x face corner) terminal) =
        word (Sum.inl (copy, Sum.inl
          (xStarFaceQZEdge P x face corner, terminal))))
      (rxCxH1_qzZero_terminal_of_qzOne
        P A3 x S word hword copy face hselected)
      hselected
      corner
end QEC.Coding.BDL26RXLocalReplacement
