-- Prove2me | solution 1 for QEC.Coding.BDL26RXSeedSmallSupport.seed_local_column_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:36:27.217071+00:00
-- url     : https://prove2.me/submissions/a41dc4db-5a28-4303-b7f6-f00e60e873cb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionBoundaryEdgeStart_ne_end
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionFaceEdgeMatrix_eq_one_iff
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalWordPush_single
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
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_boundaryArmVertex_end
import Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_boundaryArmVertex_start
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
namespace QEC.Coding.BDL26RXSeedSmallSupport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
private theorem subdivision_edge_has_face
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (x : P.X) (S : OddScale) (edge : SubdivisionEdge P x S) :
    ∃ face : SubdivisionFace P x S,
      subdivisionFaceEdgeMatrix P x S edge face = 1 := by
  let first : Fin S.half := ⟨0, S.half_pos⟩
  let last : Fin S.half := ⟨S.half - 1, by have := S.half_pos; omega⟩
  have hlast : last.val + 1 = S.half := by
    dsimp [last]
    have := S.half_pos
    omega
  rcases edge with ⟨⟨oldEdge, member⟩, k⟩ | (⟨face, i, j⟩ | ⟨face, i, j⟩)
  · rcases oldEdge with radial | boundary
    · obtain ⟨⟨face, side⟩, howner⟩ := A.xRadialFaceOwner x radial member
      fin_cases side
      · refine ⟨(face, k, first), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
        refine ⟨(0, 0), ?_⟩
        change subdivisionHorizontalEdge P x S face k first.castSucc = _
        simp [subdivisionFaceBoundaryEdge, subdivisionHorizontalEdge,
          first]
        exact howner
      · refine ⟨(face, first, k), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
        refine ⟨(1, 0), ?_⟩
        change subdivisionVerticalEdge P x S face first.castSucc k = _
        simp [subdivisionFaceBoundaryEdge, subdivisionVerticalEdge,
          first]
        exact howner
    · obtain ⟨⟨face, side⟩, howner⟩ := A.xBoundaryFaceOwner x boundary member
      fin_cases side
      · refine ⟨(face, last, k), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
        refine ⟨(1, 1), ?_⟩
        change subdivisionVerticalEdge P x S face last.succ k = _
        simp [subdivisionFaceBoundaryEdge, subdivisionVerticalEdge,
          hlast, Nat.ne_of_gt S.half_pos]
        exact howner
      · refine ⟨(face, k, last), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
        refine ⟨(0, 1), ?_⟩
        change subdivisionHorizontalEdge P x S face k last.succ = _
        simp [subdivisionFaceBoundaryEdge, subdivisionHorizontalEdge,
          hlast, Nat.ne_of_gt S.half_pos]
        exact howner
  · let before : Fin S.half := ⟨j.val, by have := j.isLt; omega⟩
    have hzero : j.val + 1 ≠ 0 := by omega
    have hlast : j.val + 1 ≠ S.half := by have := j.isLt; omega
    refine ⟨(face, i, before), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
    refine ⟨(0, 1), ?_⟩
    change subdivisionHorizontalEdge P x S face i before.succ = _
    simp [subdivisionFaceBoundaryEdge, subdivisionHorizontalEdge,
      before, hzero, hlast, Fin.ext_iff]
    rfl
  · let before : Fin S.half := ⟨i.val, by have := i.isLt; omega⟩
    have hzero : i.val + 1 ≠ 0 := by omega
    have hlast : i.val + 1 ≠ S.half := by have := i.isLt; omega
    refine ⟨(face, before, j), (subdivisionFaceEdgeMatrix_eq_one_iff P x S _ _).2 ?_⟩
    refine ⟨(1, 1), ?_⟩
    change subdivisionVerticalEdge P x S face before.succ j = _
    simp [subdivisionFaceBoundaryEdge, subdivisionVerticalEdge,
      before, hzero, hlast, Fin.ext_iff]
    rfl
private theorem seed_radial_eq (x : baseTannerSquarePresentation.X)
    (f g : XStarFace baseTannerSquarePresentation x) (a b : Two) :
    xStarFaceXQEdge baseTannerSquarePresentation x f a =
        xStarFaceXQEdge baseTannerSquarePresentation x g b ↔
      a = b ∧ (a = 1 ∨ f = g) := by
  decide +kernel +revert
private theorem seed_other_face (x : baseTannerSquarePresentation.X)
    (f : XStarFace baseTannerSquarePresentation x) :
    ∃ g : XStarFace baseTannerSquarePresentation x, g ≠ f := by
  decide +kernel +revert
private theorem subdivision_incidence_iff_four
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : SubdivisionEdge P x S) (f : XStarFace P x)
    (i j : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S edge (f, i, j) = 1 ↔
      subdivisionHorizontalEdge P x S f i j.castSucc = edge ∨
      subdivisionHorizontalEdge P x S f i j.succ = edge ∨
      subdivisionVerticalEdge P x S f i.castSucc j = edge ∨
      subdivisionVerticalEdge P x S f i.succ j = edge := by
  rw [subdivisionFaceEdgeMatrix_eq_one_iff]
  simp only [Prod.exists, Fin.exists_fin_two,
    subdivisionFaceBoundaryEdge_zero_zero, subdivisionFaceBoundaryEdge_zero_one,
    subdivisionFaceBoundaryEdge_one_zero, subdivisionFaceBoundaryEdge_one_one]
  change ((subdivisionHorizontalEdge P x S f i j.castSucc = edge ∨
    subdivisionHorizontalEdge P x S f i j.succ = edge) ∨
    subdivisionVerticalEdge P x S f i.castSucc j = edge ∨
    subdivisionVerticalEdge P x S f i.succ j = edge) ↔ _
  tauto
private theorem horizontal_normal (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half + 1)) :
    subdivisionHorizontalEdge P x S f i j =
      if h0 : j.val = 0 then Sum.inl (xStarFaceXQEdge P x f 0, i)
      else if hm : j.val = S.half then Sum.inl (xStarFaceQZEdge P x f 1, i)
      else Sum.inr (Sum.inl (f, i, (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin (S.half - 1)))) := rfl
private theorem vertical_normal (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1)) (j : Fin S.half) :
    subdivisionVerticalEdge P x S f i j =
      if h0 : i.val = 0 then Sum.inl (xStarFaceXQEdge P x f 1, j)
      else if hm : i.val = S.half then Sum.inl (xStarFaceQZEdge P x f 0, j)
      else Sum.inr (Sum.inr (f, (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (S.half - 1)), j)) := rfl
private theorem radial_ne_boundary (P : TannerSquarePresentation) (x : P.X)
    (f g : XStarFace P x) (a b : Two) :
    xStarFaceXQEdge P x f a ≠ xStarFaceQZEdge P x g b := by
  intro h
  have hv := congrArg Subtype.val h
  cases hv
private theorem boundary_ne_radial (P : TannerSquarePresentation) (x : P.X)
    (f g : XStarFace P x) (a b : Two) :
    xStarFaceQZEdge P x f a ≠ xStarFaceXQEdge P x g b :=
  Ne.symm (radial_ne_boundary P x g f b a)
private theorem horizontal_radial_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i k : Fin S.half) (j : Fin (S.half + 1)) (a : Two) :
    subdivisionHorizontalEdge P x S f i j = Sum.inl (xStarFaceXQEdge P x g a, k) ↔
      j.val = 0 ∧ xStarFaceXQEdge P x f 0 = xStarFaceXQEdge P x g a ∧ i = k := by
  by_cases h0 : j.val = 0
  · simp [horizontal_normal, h0]
  · by_cases hm : j.val = S.half <;>
      simp [horizontal_normal, h0, hm, S.half_pos.ne', boundary_ne_radial]
private theorem vertical_radial_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half + 1)) (j k : Fin S.half) (a : Two) :
    subdivisionVerticalEdge P x S f i j = Sum.inl (xStarFaceXQEdge P x g a, k) ↔
      i.val = 0 ∧ xStarFaceXQEdge P x f 1 = xStarFaceXQEdge P x g a ∧ j = k := by
  by_cases h0 : i.val = 0
  · simp [vertical_normal, h0]
  · by_cases hm : i.val = S.half <;>
      simp [vertical_normal, h0, hm, S.half_pos.ne', boundary_ne_radial]
private theorem horizontal_interior_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i k : Fin S.half) (j : Fin (S.half + 1))
    (l : Fin (S.half - 1)) :
    subdivisionHorizontalEdge P x S f i j = Sum.inr (Sum.inl (g, k, l)) ↔
      j.val ≠ 0 ∧ j.val ≠ S.half ∧ f = g ∧ i = k ∧ j.val - 1 = l.val := by
  by_cases h0 : j.val = 0
  · simp [horizontal_normal, h0]
  · by_cases hm : j.val = S.half <;>
      simp [horizontal_normal, h0, hm, S.half_pos.ne', Fin.ext_iff]
private theorem vertical_interior_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half + 1)) (j l : Fin S.half)
    (k : Fin (S.half - 1)) :
    subdivisionVerticalEdge P x S f i j = Sum.inr (Sum.inr (g, k, l)) ↔
      i.val ≠ 0 ∧ i.val ≠ S.half ∧ f = g ∧ i.val - 1 = k.val ∧ j = l := by
  by_cases h0 : i.val = 0
  · simp [vertical_normal, h0]
  · by_cases hm : i.val = S.half <;>
      simp [vertical_normal, h0, hm, S.half_pos.ne', Fin.ext_iff]
private theorem horizontal_ne_vertical_interior
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i l : Fin S.half) (j : Fin (S.half + 1))
    (k : Fin (S.half - 1)) :
    subdivisionHorizontalEdge P x S f i j ≠ Sum.inr (Sum.inr (g, k, l)) := by
  by_cases h0 : j.val = 0
  · simp [horizontal_normal, h0]
  · by_cases hm : j.val = S.half <;> simp [horizontal_normal, h0, hm, S.half_pos.ne']
private theorem vertical_ne_horizontal_interior
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half + 1)) (j k : Fin S.half)
    (l : Fin (S.half - 1)) :
    subdivisionVerticalEdge P x S f i j ≠ Sum.inr (Sum.inl (g, k, l)) := by
  by_cases h0 : i.val = 0
  · simp [vertical_normal, h0]
  · by_cases hm : i.val = S.half <;> simp [vertical_normal, h0, hm, S.half_pos.ne']
private theorem seed_radial_incidence (S : OddScale) (x : baseTannerSquarePresentation.X)
    (f g : XStarFace baseTannerSquarePresentation x) (side : Two)
    (k i j : Fin S.half) :
    subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
      (Sum.inl (xStarFaceXQEdge baseTannerSquarePresentation x f side, k))
      (g, i, j) = 1 ↔
      (side = 0 ∧ f = g ∧ k = i ∧ j.val = 0) ∨
        (side = 1 ∧ i.val = 0 ∧ k = j) := by
  rw [subdivision_incidence_iff_four]
  simp only [horizontal_radial_iff, vertical_radial_iff, seed_radial_eq,
    Fin.val_castSucc, Fin.val_succ]
  fin_cases side <;>
    simp [eq_comm, and_assoc, and_left_comm, and_comm]
private theorem interior_horizontal_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i i' j' : Fin S.half) (j : Fin (S.half - 1)) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j)))
      (g, i', j') = 1 ↔ f = g ∧ i = i' ∧
        (j'.val = j.val ∨ j'.val = j.val + 1) := by
  rw [subdivision_incidence_iff_four]
  simp only [horizontal_interior_iff, vertical_ne_horizontal_interior,
    Fin.val_castSucc, Fin.val_succ, or_false]
  have hj := j.isLt
  have hj' := j'.isLt
  by_cases hf : f = g
  · subst g
    by_cases hi : i = i'
    · subst i'
      simp only [true_and]
      omega
    · simp [hi, Ne.symm hi]
  · simp [hf, Ne.symm hf]
private theorem interior_vertical_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half - 1)) (j i' j' : Fin S.half) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (f, i, j)))
      (g, i', j') = 1 ↔ f = g ∧ j = j' ∧
        (i'.val = i.val ∨ i'.val = i.val + 1) := by
  rw [subdivision_incidence_iff_four]
  simp only [vertical_interior_iff, horizontal_ne_vertical_interior,
    Fin.val_castSucc, Fin.val_succ, false_or]
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases hf : f = g
  · subst g
    by_cases hj : j = j'
    · subst j'
      simp only [true_and, and_true]
      omega
    · simp [hj, Ne.symm hj]
  · simp [hf, Ne.symm hf]
private theorem radial_columns_equal (S : OddScale) (x : baseTannerSquarePresentation.X)
    (f g : XStarFace baseTannerSquarePresentation x) (a b : Two)
    (k l : Fin S.half)
    (h : ∀ (face : XStarFace baseTannerSquarePresentation x) (i j : Fin S.half),
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inl (xStarFaceXQEdge baseTannerSquarePresentation x f a, k))
          (face, i, j) = 1 ↔
        subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inl (xStarFaceXQEdge baseTannerSquarePresentation x g b, l))
          (face, i, j) = 1) :
    (xStarFaceXQEdge baseTannerSquarePresentation x f a, k) =
      (xStarFaceXQEdge baseTannerSquarePresentation x g b, l) := by
  let zero : Fin S.half := ⟨0, S.half_pos⟩
  simp only [seed_radial_incidence] at h
  fin_cases a <;> fin_cases b
  · have hh := (h f k zero).mp (by simp [zero])
    have heq : g = f ∧ l = k := by simpa [zero] using hh
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  · obtain ⟨other, hother⟩ := seed_other_face x f
    have hh := (h other zero l).mpr (by simp [zero])
    simp [hother, Ne.symm hother] at hh
  · obtain ⟨other, hother⟩ := seed_other_face x g
    have hh := (h other zero k).mp (by simp [zero])
    simp [hother, Ne.symm hother] at hh
  · have hh := (h f zero k).mp (by simp [zero])
    have hkl : l = k := by simpa [zero] using hh
    subst l
    exact congrArg (fun e => (e, k))
      ((seed_radial_eq x f g 1 1).2 ⟨rfl, Or.inl rfl⟩)
private theorem radial_not_horizontal (S : OddScale) (x : baseTannerSquarePresentation.X)
    (f g : XStarFace baseTannerSquarePresentation x) (a : Two)
    (k i : Fin S.half) (j : Fin (S.half - 1))
    (h : ∀ (face : XStarFace baseTannerSquarePresentation x) (r s : Fin S.half),
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inl (xStarFaceXQEdge baseTannerSquarePresentation x f a, k))
          (face, r, s) = 1 ↔
        subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inr (Sum.inl (g, i, j))) (face, r, s) = 1) : False := by
  let below : Fin S.half := ⟨j.val, by have := j.isLt; omega⟩
  let above : Fin S.half := ⟨j.val + 1, by have := j.isLt; omega⟩
  simp only [seed_radial_incidence, interior_horizontal_incidence] at h
  have hb := (h g i below).mpr (by simp [below])
  have ha := (h g i above).mpr (by simp [above])
  fin_cases a <;> simp [below, above, Fin.ext_iff] at hb ha <;> omega
private theorem radial_not_vertical (S : OddScale) (x : baseTannerSquarePresentation.X)
    (f g : XStarFace baseTannerSquarePresentation x) (a : Two)
    (k j : Fin S.half) (i : Fin (S.half - 1))
    (h : ∀ (face : XStarFace baseTannerSquarePresentation x) (r s : Fin S.half),
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inl (xStarFaceXQEdge baseTannerSquarePresentation x f a, k))
          (face, r, s) = 1 ↔
        subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S
          (Sum.inr (Sum.inr (g, i, j))) (face, r, s) = 1) : False := by
  let before : Fin S.half := ⟨i.val, by have := i.isLt; omega⟩
  let after : Fin S.half := ⟨i.val + 1, by have := i.isLt; omega⟩
  simp only [seed_radial_incidence, interior_vertical_incidence] at h
  have hb := (h g before j).mpr (by simp [before])
  have ha := (h g after j).mpr (by simp [after])
  fin_cases a <;> simp [before, after, Fin.ext_iff] at hb ha <;> omega
private theorem horizontal_columns_equal (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (f g : XStarFace P x)
    (i k : Fin S.half) (j l : Fin (S.half - 1))
    (h : ∀ (face : XStarFace P x) (r s : Fin S.half),
      subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j))) (face, r, s) = 1 ↔
        subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (g, k, l))) (face, r, s) = 1) :
    (f, i, j) = (g, k, l) := by
  let below : Fin S.half := ⟨j.val, by have := j.isLt; omega⟩
  let above : Fin S.half := ⟨j.val + 1, by have := j.isLt; omega⟩
  simp only [interior_horizontal_incidence] at h
  have hb := (h f i below).mp (by simp [below])
  have ha := (h f i above).mp (by simp [above])
  have hfg : f = g := hb.1.symm
  have hik : i = k := hb.2.1.symm
  have hjl : j = l := by
    apply Fin.ext
    dsimp [below, above] at hb ha
    omega
  rw [hfg, hik, hjl]
private theorem vertical_columns_equal (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (f g : XStarFace P x)
    (i k : Fin (S.half - 1)) (j l : Fin S.half)
    (h : ∀ (face : XStarFace P x) (r s : Fin S.half),
      subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (f, i, j))) (face, r, s) = 1 ↔
        subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (g, k, l))) (face, r, s) = 1) :
    (f, i, j) = (g, k, l) := by
  let before : Fin S.half := ⟨i.val, by have := i.isLt; omega⟩
  let after : Fin S.half := ⟨i.val + 1, by have := i.isLt; omega⟩
  simp only [interior_vertical_incidence] at h
  have hb := (h f before j).mp (by simp [before])
  have ha := (h f after j).mp (by simp [after])
  have hfg : f = g := hb.1.symm
  have hjl : j = l := hb.2.1.symm
  have hik : i = k := by
    apply Fin.ext
    dsimp [before, after] at hb ha
    omega
  rw [hfg, hik, hjl]
private theorem horizontal_not_vertical (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) (f g : XStarFace P x)
    (i l : Fin S.half) (j k : Fin (S.half - 1))
    (h : ∀ (face : XStarFace P x) (r s : Fin S.half),
      subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j))) (face, r, s) = 1 ↔
        subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (g, k, l))) (face, r, s) = 1) : False := by
  let below : Fin S.half := ⟨j.val, by have := j.isLt; omega⟩
  let above : Fin S.half := ⟨j.val + 1, by have := j.isLt; omega⟩
  simp only [interior_horizontal_incidence, interior_vertical_incidence] at h
  have hb := (h f i below).mp (by simp [below])
  have ha := (h f i above).mp (by simp [above])
  have hb' := congrArg Fin.val hb.2.1
  have ha' := congrArg Fin.val ha.2.1
  dsimp [below, above] at hb' ha'
  omega
private theorem seed_subdivision_columns_injective (S : OddScale) (x : baseTannerSquarePresentation.X)
    (a b : SubdivisionEdge baseTannerSquarePresentation x S)
    (h : ∀ face, subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S a face =
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S b face)
    (hb : ∀ edge : SubdivisionBoundaryEdge baseTannerSquarePresentation x S,
      a = edge.val ↔ b = edge.val) : a = b := by
  have hinc (face : XStarFace baseTannerSquarePresentation x) (i j : Fin S.half) :
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S a (face, i, j) = 1 ↔
      subdivisionFaceEdgeMatrix baseTannerSquarePresentation x S b (face, i, j) = 1 := by
    rw [h]
  have hboundary (e : SubdivisionEdge baseTannerSquarePresentation x S)
      (he : subdivisionBoundaryEdgeMember baseTannerSquarePresentation x S e = true) :
      a = e ↔ b = e := hb ⟨e, he⟩
  rcases a with ⟨⟨oldA, memA⟩, k⟩ | (⟨f, i, j⟩ | ⟨f, i, j⟩)
  · rcases oldA with radialA | boundaryA
    · obtain ⟨⟨f, sideA⟩, hf⟩ :=
        baseTannerSquareAdmissibleV4.xRadialFaceOwner x radialA memA
      rw [← hf] at hinc ⊢
      rcases b with ⟨⟨oldB, memB⟩, l⟩ | (⟨g, r, s⟩ | ⟨g, r, s⟩)
      · rcases oldB with radialB | boundaryB
        · obtain ⟨⟨g, sideB⟩, hg⟩ :=
            baseTannerSquareAdmissibleV4.xRadialFaceOwner x radialB memB
          rw [← hg] at hinc ⊢
          exact congrArg Sum.inl (radial_columns_equal S x f g sideA sideB k l hinc)
        · have heq := (hboundary (Sum.inl (⟨Sum.inr boundaryB, memB⟩, l)) memB).mpr rfl
          cases heq
      · exact (radial_not_horizontal S x f g sideA k r s hinc).elim
      · exact (radial_not_vertical S x f g sideA k s r hinc).elim
    · exact ((hboundary (Sum.inl (⟨Sum.inr boundaryA, memA⟩, k)) memA).mp rfl).symm
  · rcases b with ⟨⟨oldB, memB⟩, l⟩ | (⟨g, r, s⟩ | ⟨g, r, s⟩)
    · rcases oldB with radialB | boundaryB
      · obtain ⟨⟨g, sideB⟩, hg⟩ :=
          baseTannerSquareAdmissibleV4.xRadialFaceOwner x radialB memB
        rw [← hg] at hinc
        exact (radial_not_horizontal S x g f sideB l i j
          (fun face r s => (hinc face r s).symm)).elim
      · exact (hboundary (Sum.inl (⟨Sum.inr boundaryB, memB⟩, l)) memB).mpr rfl
    · exact congrArg (fun p => Sum.inr (Sum.inl p))
        (horizontal_columns_equal _ S x f g i r j s hinc)
    · exact (horizontal_not_vertical _ S x f g i s j r hinc).elim
  · rcases b with ⟨⟨oldB, memB⟩, l⟩ | (⟨g, r, s⟩ | ⟨g, r, s⟩)
    · rcases oldB with radialB | boundaryB
      · obtain ⟨⟨g, sideB⟩, hg⟩ :=
          baseTannerSquareAdmissibleV4.xRadialFaceOwner x radialB memB
        rw [← hg] at hinc
        exact (radial_not_vertical S x g f sideB l j i
          (fun face r s => (hinc face r s).symm)).elim
      · exact (hboundary (Sum.inl (⟨Sum.inr boundaryB, memB⟩, l)) memB).mpr rfl
    · exact (horizontal_not_vertical _ S x g f r j s i
        (fun face r s => (hinc face r s).symm)).elim
    · exact congrArg (fun p => Sum.inr (Sum.inr p))
        (vertical_columns_equal _ S x f g i r j s hinc)
private theorem vertical_incidence_iff (P : TannerSquarePresentation)
    (x : P.X) (S : OddScale) (v : SubdivisionBoundaryVertex P x S)
    (e : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inr v) (Sum.inr e) = 1 ↔
      v = subdivisionBoundaryEdgeStart P x S e ∨
        v = subdivisionBoundaryEdgeEnd P x S e := by
  classical
  have hne := subdivisionBoundaryEdgeStart_ne_end P x S e
  by_cases hs : v = subdivisionBoundaryEdgeStart P x S e
  · have he : v ≠ subdivisionBoundaryEdgeEnd P x S e := by simpa [hs] using hne
    simp [doubleCylinderFaceEdgeMatrix, hs, he, hne, Ne.symm hne]
  · by_cases he : v = subdivisionBoundaryEdgeEnd P x S e <;>
      simp [doubleCylinderFaceEdgeMatrix, hs, he, hne, Ne.symm hne]
private theorem boundary_predicate_constant
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (R : SubdivisionBoundaryVertex P x S → Prop)
    (hR : ∀ edge, R (subdivisionBoundaryEdgeStart P x S edge) ↔
      R (subdivisionBoundaryEdgeEnd P x S edge)) :
    ∀ v, R v ↔ R (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)) := by
  have harm (edge : XStarBoundaryEdge P x) (i : Fin (S.half + 1)) :
      R (BDL26XLocalRadialParity.boundaryArmVertex P x S edge i) ↔
        R (BDL26XLocalRadialParity.boundaryArmVertex P x S edge 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
        have hstep := hR (subdivisionOriginalBoundaryEdge P x S edge i)
        rw [BDL26XLocalRadialParity.boundaryArmVertex_start,
          BDL26XLocalRadialParity.boundaryArmVertex_end] at hstep
        exact hstep.symm.trans ih
  have hold (edge : XStarBoundaryEdge P x) :
      R (subdivisionOriginalBoundaryVertex P x S (xBoundaryEdgeStart P x edge)) ↔
        R (subdivisionOriginalBoundaryVertex P x S (xBoundaryEdgeEnd P x edge)) := by
    simpa [BDL26XLocalRadialParity.boundaryArmVertex, S.half_pos.ne'] using
      (harm edge (Fin.last S.half)).symm
  have horiginal (v : XStarBoundaryVertex P x) :
      R (subdivisionOriginalBoundaryVertex P x S v) ↔
        R (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)) := by
    induction A.xBoundaryPath x v with
    | nil => rfl
    | @step u v path edge connects ih =>
        have hstep := hold edge
        rcases connects with ⟨hs, he⟩ | ⟨hs, he⟩
        · rw [hs, he] at hstep
          exact hstep.symm.trans ih
        · rw [hs, he] at hstep
          exact hstep.trans ih
  rintro ⟨v, hv⟩
  rcases v with old | (⟨edge, i⟩ | interior)
  · exact horiginal ⟨old.val, hv⟩
  · let oldEdge : XStarBoundaryEdge P x := ⟨edge.val, hv⟩
    let step : Fin (S.half + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
    have hzero : i.val + 1 ≠ 0 := by omega
    have hlast : i.val + 1 ≠ S.half := by have := i.isLt; omega
    have h := (harm oldEdge step).trans (horiginal (xBoundaryEdgeStart P x oldEdge))
    simpa [BDL26XLocalRadialParity.boundaryArmVertex, step, hzero, hlast,
      oldEdge, xStarBoundaryEdgeToStar, Fin.ext_iff] using h
  · simp [subdivisionBoundaryVertexMember] at hv
private theorem original_boundary_vertex_injective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Function.Injective (subdivisionOriginalBoundaryVertex P x S) := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  have hs := Sum.inl.inj hv
  exact congrArg (fun v : XStarVertex P x => v.val) hs
private theorem seed_three_boundary_vertices (x : baseTannerSquarePresentation.X) :
    ∃ a b c : XStarBoundaryVertex baseTannerSquarePresentation x,
      a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  decide +kernel +revert
private theorem seed_vertical_columns_injective (S : OddScale)
    (x : baseTannerSquarePresentation.X)
    (a b : SubdivisionBoundaryVertex baseTannerSquarePresentation x S)
    (h : ∀ edge : SubdivisionBoundaryEdge baseTannerSquarePresentation x S,
      doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S (Sum.inr a) (Sum.inr edge) =
        doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S (Sum.inr b) (Sum.inr edge)) :
    a = b := by
  by_contra hab
  let R := fun v : SubdivisionBoundaryVertex baseTannerSquarePresentation x S => v = a ∨ v = b
  have hR (edge : SubdivisionBoundaryEdge baseTannerSquarePresentation x S) :
      R (subdivisionBoundaryEdgeStart baseTannerSquarePresentation x S edge) ↔
        R (subdivisionBoundaryEdgeEnd baseTannerSquarePresentation x S edge) := by
    have hi : (a = subdivisionBoundaryEdgeStart baseTannerSquarePresentation x S edge ∨
        a = subdivisionBoundaryEdgeEnd baseTannerSquarePresentation x S edge) ↔
        (b = subdivisionBoundaryEdgeStart baseTannerSquarePresentation x S edge ∨
        b = subdivisionBoundaryEdgeEnd baseTannerSquarePresentation x S edge) := by
      rw [← vertical_incidence_iff, ← vertical_incidence_iff, h edge]
    dsimp [R]
    constructor
    · rintro (hs | hs)
      · rcases hi.mp (Or.inl hs.symm) with hb | hb
        · exact (hab (hs.symm.trans hb.symm)).elim
        · exact Or.inr hb.symm
      · rcases hi.mpr (Or.inl hs.symm) with ha | ha
        · exact (hab (ha.trans hs)).elim
        · exact Or.inl ha.symm
    · rintro (he | he)
      · rcases hi.mp (Or.inr he.symm) with hb | hb
        · exact Or.inr hb.symm
        · exact (hab (he.symm.trans hb.symm)).elim
      · rcases hi.mpr (Or.inr he.symm) with ha | ha
        · exact Or.inl ha.symm
        · exact (hab (ha.trans he)).elim
  have hc := boundary_predicate_constant baseTannerSquarePresentation
    baseTannerSquareAdmissible x S R hR
  have hall (v : SubdivisionBoundaryVertex baseTannerSquarePresentation x S) : R v :=
    (hc v).mpr ((hc a).mp (Or.inl rfl))
  obtain ⟨u, v, w, huv, huw, hvw⟩ := seed_three_boundary_vertices x
  have inj := original_boundary_vertex_injective baseTannerSquarePresentation x S
  have huv' := inj.ne huv
  have huw' := inj.ne huw
  have hvw' := inj.ne hvw
  have hu := hall (subdivisionOriginalBoundaryVertex baseTannerSquarePresentation x S u)
  have hv := hall (subdivisionOriginalBoundaryVertex baseTannerSquarePresentation x S v)
  have hw := hall (subdivisionOriginalBoundaryVertex baseTannerSquarePresentation x S w)
  dsimp [R] at hu hv hw
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  all_goals aesop
end QEC.Coding.BDL26RXSeedSmallSupport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXSeedSmallSupport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RXSeedSmallSupport
theorem _root_.solution (S : OddScale)
    (x : baseTannerSquarePresentation.X) :
    Function.Injective (fun edge : DoubleCylinderEdge baseTannerSquarePresentation x S =>
      fun face : DoubleCylinderFace baseTannerSquarePresentation x S =>
        doubleCylinderFaceEdgeMatrix baseTannerSquarePresentation x S edge face) := by
  classical
  intro a b h
  rcases a with ⟨copyA, a⟩ | a
  · obtain ⟨face, hface⟩ := subdivision_edge_has_face baseTannerSquarePresentation
      baseTannerSquareAdmissibleV4 x S a
    have ha := congrFun h (Sum.inl (copyA, face))
    rcases b with ⟨copyB, b⟩ | b
    · have hcopy : copyA = copyB := by
        by_contra hne
        simp [doubleCylinderFaceEdgeMatrix, hface, Ne.symm hne] at ha
      subst copyB
      have heq : a = b := seed_subdivision_columns_injective S x a b
        (fun cell => by
          have hh := congrFun h (Sum.inl (copyA, cell))
          simpa [doubleCylinderFaceEdgeMatrix] using hh)
        (fun rectangle => by
          have hh := congrFun h (Sum.inr rectangle)
          simp only [doubleCylinderFaceEdgeMatrix] at hh
          by_cases ha : a = rectangle.val
          · by_cases hb : b = rectangle.val
            · simp [ha, hb]
            · have bad : (1 : BDL26FiniteTannerSquare.Field) = 0 := by simpa [ha, hb] using hh
              exact (one_ne_zero bad).elim
          · by_cases hb : b = rectangle.val
            · have bad : (0 : BDL26FiniteTannerSquare.Field) = 1 := by simpa [ha, hb] using hh
              exact (zero_ne_one bad).elim
            · simp [ha, hb])
      exact congrArg (fun e => Sum.inl (copyA, e)) heq
    · simp [doubleCylinderFaceEdgeMatrix, hface] at ha
  · rcases b with ⟨copyB, b⟩ | b
    · obtain ⟨face, hface⟩ := subdivision_edge_has_face baseTannerSquarePresentation
        baseTannerSquareAdmissibleV4 x S b
      have hb := congrFun h (Sum.inl (copyB, face))
      simp [doubleCylinderFaceEdgeMatrix, hface] at hb
    · exact congrArg Sum.inr (seed_vertical_columns_injective S x a b
        (fun edge => congrFun h (Sum.inr edge)))
end QEC.Coding.BDL26RXSeedSmallSupport
