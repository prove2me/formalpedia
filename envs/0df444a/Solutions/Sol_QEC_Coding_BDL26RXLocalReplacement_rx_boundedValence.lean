-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rx_boundedValence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:08:16.158188+00:00
-- url     : https://prove2.me/submissions/a2266bde-01b7-4fdd-957b-977ba2e76aa9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_sharedQ_card_le_two
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_card
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_TannerSquarePresentation_faceQ_injective
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderEndInclusion_apply
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
private theorem rxStarEdgeInteriorOuterQ_cases
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (candidate : RXFace P S) (corner : Two)
    (houter : RXStarEdgeInteriorOuterFace
      P A4 S x copy edge member index candidate) :
    rxFaceQ P S candidate corner = localFaceQAt P S
        (rxStarEdgeInteriorRectangleBeforeLocalFace
          P S x copy edge member index) 0 ∨
      rxFaceQ P S candidate corner = localFaceQAt P S
        (rxStarEdgeInteriorRectangleBeforeLocalFace
          P S x copy edge member index) 1 ∨
      rxFaceQ P S candidate corner = localFaceQAt P S
        (rxStarEdgeInteriorRectangleAfterLocalFace
          P S x copy edge member index) 0 ∨
      rxFaceQ P S candidate corner = localFaceQAt P S
        (rxStarEdgeInteriorRectangleAfterLocalFace
          P S x copy edge member index) 1 ∨
      rxFaceQ P S candidate corner = glueFaceQ0 P S
        (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index) ∨
      rxFaceQ P S candidate corner = glueFaceQ1 P S
        (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index) ∨
      rxFaceQ P S candidate corner = glueFaceQ0 P S
        (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index) ∨
      rxFaceQ P S candidate corner = glueFaceQ1 P S
        (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index) := by
  rcases houter with hbeforeRect | hafterRect | hbeforeGlue | hafterGlue
  · subst candidate
    fin_cases corner
    · left; rfl
    · right; left; rfl
  · subst candidate
    fin_cases corner
    · right; right; left; rfl
    · right; right; right; left; rfl
  · subst candidate
    fin_cases corner
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
  · subst candidate
    fin_cases corner
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; rfl
open BDL26BoundedValence
private theorem rxFaceInterior_xq_card_le_four
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x) (i j : Fin (S.half - 1)) :
    Fintype.card {q : RX1 P S //
      rxXQIncidence P S ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ q = true} ≤ 4 := by
  classical
  let a := localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 0
  let b := localFaceQAt P S (rxFaceInteriorLocalFaceSW P S x copy face i j) 1
  let c := localFaceQAt P S (rxFaceInteriorLocalFaceSE P S x copy face i j) 0
  let d := localFaceQAt P S (rxFaceInteriorLocalFaceNW P S x copy face i j) 1
  have cover : ∀ q, rxXQIncidence P S
      ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ q = true →
      q ∈ ({a, b, c, d} : Finset (RX1 P S)) := by
    intro q hq
    obtain ⟨candidate, corner, hx, hc⟩ :=
      (rxXQIncidence_eq_true_iff P S _ q).1 hq
    have member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ (Vertex.q q) = true := by
      simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
      refine ⟨candidate, ?_, ?_⟩
      · unfold xStarFaceMember
        apply decide_eq_true
        exact hx
      · fin_cases corner
        · exact Or.inl hc.symm
        · exact Or.inr hc.symm
    have cases := rxFaceInteriorBoundaryQ_cases P S x copy face i j q member
    obtain ⟨hSWSE, hSWNW, hSENE, hNWNE⟩ :=
      rxFaceInteriorNeighborQ_eq P S x copy face i j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases cases with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl (h.trans hSWSE.symm))
    · exact Or.inl (h.trans hSWNW.symm)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl (h.trans hSENE.symm)))
    · exact Or.inr (Or.inr (Or.inr (h.trans hNWNE.symm)))
  calc
    _ = (Finset.univ.filter (fun q => rxXQIncidence P S
        ⟨x, (copy, Sum.inr (Sum.inr (face, i, j)))⟩ q = true)).card :=
      Fintype.card_subtype _
    _ ≤ ({a, b, c, d} : Finset (RX1 P S)).card := by
      apply Finset.card_le_card
      intro q hq
      exact cover q (Finset.mem_filter.mp hq).2
    _ ≤ 4 := Finset.card_le_four
private theorem rxOriginalBoundaryQNeighbour_covers
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (q : P.Q)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.q q) = true)
    (target : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q oldMember)
      (Vertex.q target) = true) :
    ∃ tag, rxOriginalBoundaryQNeighbour P A4 S x copy q oldMember tag = target := by
  rcases target with ⟨candidateX, (⟨candidateCopy, localEdge⟩ | boundaryVertex)⟩ |
    ⟨candidateQ, candidateCopy, vertex⟩
  · rcases localEdge with ⟨⟨rawEdge, edgeMember⟩, segment⟩ | interior
    · rcases rawEdge with xq | qz
      · obtain ⟨hx, hnorm⟩ := rxOriginalBoundaryQRawRadialQ_normalize
          P A4 S x copy q oldMember candidateX candidateCopy xq edgeMember segment member
        exact ⟨Sum.inr 0, (hnorm hx).symm⟩
      · obtain ⟨hx, hnorm⟩ := rxOriginalBoundaryQRawRectangleQ_normalize
          P S x copy q oldMember candidateX candidateCopy qz edgeMember segment member
        subst candidateX
        obtain ⟨hq, heq⟩ := hnorm rfl
        let e : QStarEdge P q := ⟨qz.1.2, by simpa [hq] using qz.2⟩
        refine ⟨Sum.inl e, ?_⟩
        rw [heq]
        simp only [rxOriginalBoundaryQNeighbour,
          rxOriginalBoundaryQRectangleLocalFaceAt,
          localFaceQAt, twoSelect_zero, localFaceQ0, localFaceQ0Edge,
          localFaceQ0EdgeAt, doubleCylinderRectangleBoundaryEdge_zero,
          qToXDoubleCylinderEdgeRaw, qToXSubdivisionBoundaryEdge,
          subdivisionOriginalBoundaryEdge, rxStarEdgeInteriorBoundaryEdge]
        congr 6
        apply Subtype.ext
        apply congrArg Sum.inr
        apply Subtype.ext
        exact Prod.ext hq.symm rfl
    · exact False.elim (rxOriginalBoundaryQRawInteriorQ_false
        P S x copy q oldMember candidateX candidateCopy interior member)
  · obtain ⟨hx, hnorm⟩ := rxOriginalBoundaryQRawVerticalQ_normalize
      P A4 S x copy q oldMember candidateX boundaryVertex member
    exact ⟨Sum.inr 1, (hnorm hx).symm⟩
  · rcases vertex with (center | oldZ) | interior
    · have hnorm := rxOriginalBoundaryQRawCenterQ_normalize
        P A4 S x copy q oldMember candidateQ candidateCopy center member
      exact ⟨Sum.inr 2, hnorm.2.2.symm⟩
    · have himpossible := rxOriginalBoundaryQRawQCenterTag_true
        P S x copy q oldMember
          ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inr oldZ))⟩ member
      simp [rxOriginalBoundaryQQCenterTag] at himpossible
    · have himpossible := rxOriginalBoundaryQRawQCenterTag_true
        P S x copy q oldMember
          ⟨candidateQ, (candidateCopy, Sum.inr interior)⟩ member
      simp [rxOriginalBoundaryQQCenterTag] at himpossible
private theorem xStarQZEdge_xq (P : TannerSquarePresentation) (x : P.X)
    (e : QZEdge P) (h : xStarEdgeMember P x (Sum.inr e) = true) :
    P.xq x e.1.1 = true := by
  simp only [xStarEdgeMember, decide_eq_true_eq] at h
  obtain ⟨f, hx, he⟩ := h
  have hx' : P.faceX f = x := by simpa [xStarFaceMember, rxReplacementPresentation, rxReplacementData] using hx
  change decide (e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1) = true at he
  rw [decide_eq_true_eq] at he
  rcases he with rfl | rfl
  · simpa [faceQZEdge, hx'] using P.data.faceQ_xq f 0
  · simpa [faceQZEdge, hx'] using P.data.faceQ_xq f 1
private theorem rxOriginalBoundaryZNeighbour_covers
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (z : P.Z)
    (oldMember : xStarBoundaryVertexMember P x (Vertex.z z) = true)
    (target : RX1 P S)
    (member : xStarBoundaryVertexMember (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z oldMember)
      (Vertex.q target) = true) :
    ∃ tag, rxOriginalBoundaryZNeighbour P A4 S x copy z oldMember tag = target := by
  rcases target with ⟨candidateX, (⟨candidateCopy, localEdge⟩ | boundaryVertex)⟩ |
    ⟨candidateQ, candidateCopy, vertex⟩
  · rcases localEdge with ⟨⟨rawEdge, edgeMember⟩, segment⟩ | interior
    · rcases rawEdge with xq | qz
      · exact False.elim (rxOriginalBoundaryZRawXQEdgeQ_false
          P S x copy z oldMember candidateX candidateCopy xq edgeMember segment member)
      · obtain ⟨hx, hnorm⟩ := rxOriginalBoundaryZRawRectangleQ_normalize
          P S x copy z oldMember candidateX candidateCopy qz edgeMember segment member
        subst candidateX
        obtain ⟨hz, heq⟩ := hnorm rfl
        let shared : SharedQ P.data x z := ⟨qz.1.1, by
          simp [xStarQZEdge_xq P x qz edgeMember, ← hz, qz.2]⟩
        refine ⟨Sum.inl (shared, 0), ?_⟩
        rw [heq]
        simp only [rxOriginalBoundaryZNeighbour, if_pos rfl, if_true]
        congr 2
        apply Subtype.ext
        exact Prod.ext rfl hz.symm
    · exact False.elim (rxOriginalBoundaryZRawInteriorQ_false
        P S x copy z oldMember candidateX candidateCopy interior member)
  · obtain ⟨hx, hnorm⟩ := rxOriginalBoundaryZRawVerticalQ_normalize
      P A4 S x copy z oldMember candidateX boundaryVertex member
    exact ⟨Sum.inr (), (hnorm hx).symm⟩
  · rcases vertex with (center | oldZ) | interior
    · have hfalse := rxOriginalBoundaryZRawQEndpointTag_true
        P A4 S x copy z oldMember
          ⟨candidateQ, (candidateCopy, Sum.inl (Sum.inl center))⟩ member
      simp [rxOriginalBoundaryZQEndpointTag] at hfalse
    · obtain ⟨hxq, hnorm⟩ := rxOriginalBoundaryZRawQEndpoint_normalize
        P R A4 S x copy z oldMember candidateQ candidateCopy oldZ member
      obtain ⟨hz, heq⟩ := hnorm hxq
      let shared : SharedQ P.data x z := ⟨candidateQ, by simp [hxq, ← hz, oldZ.2]⟩
      refine ⟨Sum.inl (shared, 1), ?_⟩
      rw [heq]
      simp only [rxOriginalBoundaryZNeighbour, show (1 : Fin 2) ≠ 0 by decide, if_false]
      congr 2
      apply Subtype.ext
      exact Prod.ext rfl hz.symm
    · have hfalse := rxOriginalBoundaryZRawQEndpointTag_true
        P A4 S x copy z oldMember
          ⟨candidateQ, (candidateCopy, Sum.inr interior)⟩ member
      simp [rxOriginalBoundaryZQEndpointTag] at hfalse
private theorem rxRadialInteriorNeighbour_covers
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (radial : XQEdge P)
    (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (index : Fin (S.half - 1)) (target : RX1 P S)
    (h : rxXQIncidence P S
      ⟨x, (copy, Sum.inr (Sum.inl (⟨Sum.inl radial, member⟩, index)))⟩ target = true) :
    ∃ tag, rxRadialInteriorNeighbour P S x copy radial member index tag = target := by
  obtain ⟨candidate, qCorner, hx, hq⟩ := (rxXQIncidence_eq_true_iff P S _ target).1 h
  have cases := rxStarEdgeInteriorIncidentFace_cases P A4 S x copy
    ⟨Sum.inl radial, member⟩ index candidate hx
  rcases cases with ⟨face, corner, hedge, hbefore | hafter⟩ |
    ⟨boundary, boundaryMember, himpossible, _⟩
  · subst candidate
    by_cases halong : qCorner = rxStarEdgeInteriorAlongCornerAt ⟨Sum.inl radial, member⟩ corner
    · refine ⟨Sum.inr 0, ?_⟩
      have ha := rxStarEdgeInteriorBeforeAlongQAt P S x copy
        ⟨Sum.inl radial, member⟩ index face corner hedge
      exact ha.symm.trans (by simpa [rxFaceQ, localFaceQAt, halong] using hq)
    · have hacross : qCorner =
          rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inl radial, member⟩ corner := by
        fin_cases qCorner <;> fin_cases corner <;>
          simp [rxStarEdgeInteriorAlongCornerAt, rxStarEdgeInteriorAcrossCornerAt,
            rxTwoElim] at halong ⊢
      exact ⟨Sum.inl ⟨(face, corner), hedge⟩,
        by simpa [rxRadialInteriorNeighbour, rxFaceQ, localFaceQAt, hacross] using hq⟩
  · subst candidate
    by_cases halong : qCorner = rxStarEdgeInteriorAlongCornerAt ⟨Sum.inl radial, member⟩ corner
    · refine ⟨Sum.inr 1, ?_⟩
      have ha := rxStarEdgeInteriorAfterAlongQAt P S x copy
        ⟨Sum.inl radial, member⟩ index face corner hedge
      exact ha.symm.trans (by simpa [rxFaceQ, localFaceQAt, halong] using hq)
    · have hacross : qCorner =
          rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inl radial, member⟩ corner := by
        fin_cases qCorner <;> fin_cases corner <;>
          simp [rxStarEdgeInteriorAlongCornerAt, rxStarEdgeInteriorAcrossCornerAt,
            rxTwoElim] at halong ⊢
      refine ⟨Sum.inl ⟨(face, corner), hedge⟩, ?_⟩
      exact (rxStarEdgeInteriorAcrossQAt P S x copy
        ⟨Sum.inl radial, member⟩ index face corner).trans
        (by simpa [rxFaceQ, localFaceQAt, hacross] using hq)
  · cases congrArg Subtype.val himpossible
private theorem card_fiber_le_two {α : Type} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (a b : α)
    (cover : ∀ x, p x → x = a ∨ x = b) : Fintype.card {x // p x} ≤ 2 := by
  calc
    Fintype.card {x // p x} = (Finset.univ.filter p).card := Fintype.card_subtype p
    _ ≤ ({a, b} : Finset α).card := by
      apply Finset.card_le_card
      intro x hx
      have hp := (Finset.mem_filter.mp hx).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using cover x hp
    _ ≤ 2 := Finset.card_le_two
private theorem qXDegree_rx_local_le_two (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    qXDegree (rxReplacementPresentation P S) (Sum.inl ⟨x, edge⟩) ≤ 2 := by
  classical
  apply card_fiber_le_two _
    (⟨x, tannerDoubleCylinderEdgeStart P x S edge⟩ : RX0 P S)
    (⟨x, tannerDoubleCylinderEdgeEnd P x S edge⟩ : RX0 P S)
  intro vertex hvertex
  obtain ⟨face, corner, hx, hq⟩ :=
    (rxXQIncidence_eq_true_iff P S vertex (Sum.inl ⟨x, edge⟩)).1 hvertex
  obtain ⟨endpoint, hendpoint⟩ :=
    rxFaceX_eq_endpoint_of_faceQ_eq_xEdge P S face corner x edge hq
  have hv := hx.symm.trans hendpoint
  fin_cases endpoint
  · left
    simpa [BDL26RXLocalReplacement.edgeEndpoint, twoSelect] using hv
  · right
    simpa [BDL26RXLocalReplacement.edgeEndpoint, twoSelect] using hv
private theorem qXDegree_rx_shifted_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S) :
    qXDegree (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) ≤
      qXDegree P q := by
  classical
  let route : {x : RX0 P S // rxXQIncidence P S x (Sum.inr ⟨q, vertex⟩) = true} →
      {x : P.X // P.xq x q = true} := fun x =>
    ⟨x.1.1, rxQVertexXRadial_oldXQ P S x.1 q vertex x.2⟩
  apply Fintype.card_le_of_injective route
  intro a b h
  have hab : a.1.1 = b.1.1 := congrArg Subtype.val h
  obtain ⟨⟨edge, endpoint⟩, he⟩ :=
    rxQDoubleCylinderVertexIncidentEdge P A q S vertex
  have he' : edgeEndpoint (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) edge endpoint = vertex := by
    fin_cases endpoint <;> exact he
  have ha := rxQVertexGlueFaceX_eq P S a.1 q vertex a.2
    (rxQVertexXRadial_oldXQ P S a.1 q vertex a.2) edge endpoint he'
  have hb := rxQVertexGlueFaceX_eq P S b.1 q vertex b.2
    (rxQVertexXRadial_oldXQ P S b.1 q vertex b.2) edge endpoint he'
  have hglue : glueFaceX P S ⟨⟨(a.1.1, q),
      rxQVertexXRadial_oldXQ P S a.1 q vertex a.2⟩, edge, endpoint⟩ =
      glueFaceX P S ⟨⟨(b.1.1, q),
        rxQVertexXRadial_oldXQ P S b.1 q vertex b.2⟩, edge, endpoint⟩ := by
    rcases a with ⟨⟨ax, av⟩, ha'⟩
    rcases b with ⟨⟨bx, bv⟩, hb'⟩
    dsimp only at hab
    subst bx
    rfl
  exact Subtype.ext (ha.symm.trans (hglue.trans hb))
private theorem card_fiber_le_of_covered {α β : Type} [Fintype α] [Fintype β]
    (p : α → Prop) [DecidablePred p] (f : β → α)
    (cover : ∀ x, p x → ∃ y, f y = x) :
    Fintype.card {x // p x} ≤ Fintype.card β := by
  classical
  calc
    Fintype.card {x // p x} = (Finset.univ.filter p).card := Fintype.card_subtype p
    _ ≤ (Finset.univ.image f).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨y, hy⟩ := cover x (Finset.mem_filter.mp hx).2
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card β := Finset.card_univ
private theorem rx_shifted_z_cases (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (vertex : QDoubleCylinderVertex P q S) (z : RX2 P S)
    (h : rxQZIncidence P S (Sum.inr ⟨q, vertex⟩) z = true) :
    (∃ edge : QDoubleCylinderEdge P q S, ∃ endpoint : Fin 2,
      z = Sum.inl (Sum.inr ⟨q, edge⟩) ∧
      BDL26RXLocalReplacement.edgeEndpoint
        (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
        edge endpoint = vertex) ∨
    (∃ endpoint : QStarEdge P q, ∃ copy : Fin 2,
      vertex = (copy, Sum.inl (Sum.inr endpoint)) ∧
      z = Sum.inr (endpoint.1, copy)) := by
  obtain ⟨face, corner, hq, hz⟩ :=
    (rxQZIncidence_eq_true_iff P S (Sum.inr ⟨q, vertex⟩) z).1 h
  rcases face with localFace | glue | old
  · rcases localFace with ⟨x, cell, material⟩
    fin_cases corner <;>
      simp [rxFaceQ, localFaceQAt, localFaceQ0, localFaceQ1] at hq
  · rcases glue with ⟨oldEdge, edge, endpoint⟩
    fin_cases corner
    · cases hq
    · have htag := Sum.inr.inj hq
      have hold : oldEdge.1.2 = q := congrArg Sigma.fst htag
      subst q
      have hv : BDL26RXLocalReplacement.edgeEndpoint
          (qDoubleCylinderEdgeStart P oldEdge.1.2 S)
          (qDoubleCylinderEdgeEnd P oldEdge.1.2 S) edge endpoint = vertex :=
        eq_of_heq (Sigma.mk.inj_iff.mp htag).2
      exact Or.inl ⟨edge, endpoint, hz.symm, hv⟩
  · rcases old with ⟨face, copy⟩
    have htag := Sum.inr.inj hq
    have hold : P.faceQ face corner = q := congrArg Sigma.fst htag
    subst q
    have hv : (copy, Sum.inl (Sum.inr
        (⟨P.faceZ face, P.data.faceQ_qz face corner⟩ :
          QStarEdge P (P.faceQ face corner)))) = vertex :=
      eq_of_heq (Sigma.mk.inj_iff.mp htag).2
    exact Or.inr ⟨⟨P.faceZ face, P.data.faceQ_qz face corner⟩, copy,
      hv.symm, hz.symm⟩
private theorem qCylinder_cone_edge (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (copy : Fin 2) (edge : QDoubleCylinderEdge P q S)
    (endpoint : Fin 2)
    (h : BDL26RXLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
      edge endpoint = (copy, Sum.inl (Sum.inl ()))) :
    ∃ e : QStarEdge P q,
      edge = Sum.inl (copy, e, ⟨0, S.half_pos⟩) := by
  rcases edge with ⟨c, e, i⟩ | e
  · fin_cases endpoint
    · change (c, qSubdivisionEdgeStart P q S (e, i)) = _ at h
      have hc : c = copy := congrArg Prod.fst h
      subst c
      by_cases hi : i.1 = 0
      · have heq : i = ⟨0, S.half_pos⟩ := Fin.ext hi
        subst i
        exact ⟨e, rfl⟩
      · simp [qSubdivisionEdgeStart, hi] at h
    · change (c, qSubdivisionEdgeEnd P q S (e, i)) = _ at h
      by_cases hi : i.1 + 1 = S.half <;>
        simp [qSubdivisionEdgeEnd, hi, qStarEdgeEnd] at h
  · fin_cases endpoint <;>
      simp [BDL26RXLocalReplacement.edgeEndpoint, twoSelect,
        qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd, qStarEdgeEnd] at h
private theorem qZDegree_rx_cone_le (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (copy : Fin 2) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inr ⟨q, (copy, Sum.inl (Sum.inl ()))⟩) ≤ qZDegree P q := by
  classical
  apply card_fiber_le_of_covered
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inr ⟨q, (copy, Sum.inl (Sum.inl ()))⟩) z = true)
    (fun e : QStarEdge P q =>
    (Sum.inl (Sum.inr ⟨q, Sum.inl (copy, e, ⟨0, S.half_pos⟩)⟩) : RX2 P S))
  intro z hz
  rcases rx_shifted_z_cases P S q (copy, Sum.inl (Sum.inl ())) z hz with
    ⟨edge, endpoint, he, hv⟩ | ⟨oldZ, c, hv, he⟩
  · obtain ⟨e, hEdge⟩ := qCylinder_cone_edge P S q copy edge endpoint hv
    exact ⟨e, by simpa [hEdge] using he.symm⟩
  · cases congrArg Prod.snd hv
private theorem qDegree_rx_cone_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) (copy : Fin 2) :
    qXDegree (rxReplacementPresentation P S)
        (Sum.inr ⟨q, (copy, Sum.inl (Sum.inl ()))⟩) +
      qZDegree (rxReplacementPresentation P S)
        (Sum.inr ⟨q, (copy, Sum.inl (Sum.inl ()))⟩) ≤
      qXDegree P q + qZDegree P q :=
  Nat.add_le_add (qXDegree_rx_shifted_le P A S q _)
    (qZDegree_rx_cone_le P S q copy)
private theorem qCylinder_interior_edge (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (copy : Fin 2) (oldEdge : QStarEdge P q)
    (j : Fin (S.half - 1)) (edge : QDoubleCylinderEdge P q S)
    (endpoint : Fin 2)
    (h : BDL26RXLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
      edge endpoint = (copy, Sum.inr (oldEdge, j))) :
    edge = Sum.inl (copy, oldEdge, ⟨j.1, by have := j.2; omega⟩) ∨
      edge = Sum.inl (copy, oldEdge, ⟨j.1 + 1, by have := j.2; omega⟩) := by
  rcases edge with ⟨c, e, i⟩ | e
  · fin_cases endpoint
    · change (c, qSubdivisionEdgeStart P q S (e, i)) = _ at h
      have hc : c = copy := congrArg Prod.fst h
      subst c
      by_cases hi : i.1 = 0
      · simp [qSubdivisionEdgeStart, hi] at h
      · have hv := congrArg Prod.snd h
        simp only [qSubdivisionEdgeStart, dif_neg hi] at hv
        have he : e = oldEdge := congrArg Prod.fst (Sum.inr.inj hv)
        have hj : i.1 - 1 = j.1 :=
          congrArg Fin.val (congrArg Prod.snd (Sum.inr.inj hv))
        subst e
        right
        congr 3
        apply Fin.ext
        change i.1 = j.1 + 1
        omega
    · change (c, qSubdivisionEdgeEnd P q S (e, i)) = _ at h
      have hc : c = copy := congrArg Prod.fst h
      subst c
      by_cases hi : i.1 + 1 = S.half
      · simp [qSubdivisionEdgeEnd, hi] at h
      · have hv := congrArg Prod.snd h
        simp only [qSubdivisionEdgeEnd, dif_neg hi] at hv
        have he : e = oldEdge := congrArg Prod.fst (Sum.inr.inj hv)
        have hj : i.1 = j.1 :=
          congrArg Fin.val (congrArg Prod.snd (Sum.inr.inj hv))
        subst e
        left
        congr 3
        exact Fin.ext hj
  · fin_cases endpoint <;>
      simp [BDL26RXLocalReplacement.edgeEndpoint, twoSelect,
        qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd, qStarEdgeEnd] at h
private theorem qZDegree_rx_interior_le_two (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (copy : Fin 2)
    (oldEdge : QStarEdge P q) (j : Fin (S.half - 1)) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inr ⟨q, (copy, Sum.inr (oldEdge, j))⟩) ≤ 2 := by
  classical
  apply card_fiber_le_two
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inr ⟨q, (copy, Sum.inr (oldEdge, j))⟩) z = true)
    (Sum.inl (Sum.inr ⟨q, Sum.inl
      (copy, oldEdge, ⟨j.1, by have := j.2; omega⟩)⟩) : RX2 P S)
    (Sum.inl (Sum.inr ⟨q, Sum.inl
      (copy, oldEdge, ⟨j.1 + 1, by have := j.2; omega⟩)⟩) : RX2 P S)
  intro z hz
  rcases rx_shifted_z_cases P S q (copy, Sum.inr (oldEdge, j)) z hz with
    ⟨edge, endpoint, he, hv⟩ | ⟨oldZ, c, hv, he⟩
  · rcases qCylinder_interior_edge P S q copy oldEdge j edge endpoint hv with h | h
    · exact Or.inl (by simpa [h] using he)
    · exact Or.inr (by simpa [h] using he)
  · cases congrArg Prod.snd hv
private theorem qCylinder_endpoint_edge (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (copy : Fin 2) (oldEdge : QStarEdge P q)
    (edge : QDoubleCylinderEdge P q S) (endpoint : Fin 2)
    (h : BDL26RXLocalReplacement.edgeEndpoint
      (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
      edge endpoint = (copy, Sum.inl (Sum.inr oldEdge))) :
    edge = Sum.inl (copy, oldEdge, ⟨S.half - 1, by have := S.half_pos; omega⟩) ∨
      edge = Sum.inr oldEdge := by
  rcases edge with ⟨c, e, i⟩ | e
  · fin_cases endpoint
    · change (c, qSubdivisionEdgeStart P q S (e, i)) = _ at h
      by_cases hi : i.1 = 0 <;>
        simp [qSubdivisionEdgeStart, hi, qStarEdgeStart] at h
    · change (c, qSubdivisionEdgeEnd P q S (e, i)) = _ at h
      have hc : c = copy := congrArg Prod.fst h
      subst c
      by_cases hi : i.1 + 1 = S.half
      · have hv := congrArg Prod.snd h
        simp only [qSubdivisionEdgeEnd, dif_pos hi, qStarEdgeEnd] at hv
        have he : e = oldEdge := Sum.inr.inj (Sum.inl.inj hv)
        subst e
        left
        congr 3
        apply Fin.ext
        change i.1 = S.half - 1
        omega
      · simp [qSubdivisionEdgeEnd, hi] at h
  · right
    fin_cases endpoint
    all_goals
      have hv := congrArg Prod.snd h
      simp only [BDL26RXLocalReplacement.edgeEndpoint, twoSelect,
        qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd, qStarEdgeEnd] at hv
      simpa using hv
private theorem card_fiber_le_three {α : Type} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (a b c : α)
    (cover : ∀ x, p x → x = a ∨ x = b ∨ x = c) :
    Fintype.card {x // p x} ≤ 3 := by
  calc
    Fintype.card {x // p x} = (Finset.univ.filter p).card := Fintype.card_subtype p
    _ ≤ ({a, b, c} : Finset α).card := by
      apply Finset.card_le_card
      intro x hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        cover x (Finset.mem_filter.mp hx).2
    _ ≤ 3 := Finset.card_le_three
private theorem qZDegree_rx_endpoint_le_three (P : TannerSquarePresentation)
    (S : OddScale) (q : P.Q) (copy : Fin 2) (oldEdge : QStarEdge P q) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr oldEdge))⟩) ≤ 3 := by
  classical
  apply card_fiber_le_three
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inr ⟨q, (copy, Sum.inl (Sum.inr oldEdge))⟩) z = true)
    (Sum.inl (Sum.inr ⟨q, Sum.inl
      (copy, oldEdge, ⟨S.half - 1, by have := S.half_pos; omega⟩)⟩) : RX2 P S)
    (Sum.inl (Sum.inr ⟨q, Sum.inr oldEdge⟩) : RX2 P S)
    (Sum.inr (oldEdge.1, copy) : RX2 P S)
  intro z hz
  rcases rx_shifted_z_cases P S q (copy, Sum.inl (Sum.inr oldEdge)) z hz with
    ⟨edge, endpoint, he, hv⟩ | ⟨oldZ, c, hv, he⟩
  · rcases qCylinder_endpoint_edge P S q copy oldEdge edge endpoint hv with h | h
    · exact Or.inl (by simpa [h] using he)
    · exact Or.inr (Or.inl (by simpa [h] using he))
  · have hc : copy = c := congrArg Prod.fst hv
    have hold : oldEdge = oldZ :=
      Sum.inr.inj (Sum.inl.inj (congrArg Prod.snd hv))
    exact Or.inr (Or.inr (by simpa [← hc, ← hold] using he))
private theorem rx_shifted_bounded (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (h : BoundedValence P)
    (q : P.Q) (vertex : QDoubleCylinderVertex P q S) :
    qXDegree (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) ≤ 4 ∧
      qZDegree (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) ≤ 4 ∧
      qXDegree (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) +
        qZDegree (rxReplacementPresentation P S) (Sum.inr ⟨q, vertex⟩) ≤ 7 := by
  have hx := (qXDegree_rx_shifted_le P A S q vertex).trans (h.2.2 q).1
  refine ⟨hx, ?_⟩
  rcases vertex with ⟨copy, (_ | oldZ) | interior⟩
  · have hz := (qZDegree_rx_cone_le P S q copy).trans (h.2.2 q).2.1
    exact ⟨hz, (qDegree_rx_cone_le P A S q copy).trans (h.2.2 q).2.2⟩
  · have hz := qZDegree_rx_endpoint_le_three P S q copy oldZ
    constructor <;> omega
  · rcases interior with ⟨oldEdge, j⟩
    have hz := qZDegree_rx_interior_le_two P S q copy oldEdge j
    constructor <;> omega
private theorem zDegree_rx_local_le_four (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (cell : DoubleCylinderFace P x S) :
    zDegree (rxReplacementPresentation P S) (Sum.inl (Sum.inl ⟨x, cell⟩)) ≤ 4 := by
  classical
  have hcard : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  rw [← hcard]
  apply card_fiber_le_of_covered _ (rxLocalCellBoundaryEdge P S x cell)
  intro q hq
  obtain ⟨face, corner, hfaceQ, hfaceZ⟩ :=
    (rxQZIncidence_eq_true_iff P S q (Sum.inl (Sum.inl ⟨x, cell⟩))).1 hq
  rcases face with ⟨oldX, oldCell, bits⟩ | glue | old
  · have hcell : (⟨oldX, oldCell⟩ : Σ y : P.X, DoubleCylinderFace P y S) =
        ⟨x, cell⟩ := Sum.inl.inj (Sum.inl.inj hfaceZ)
    cases hcell
    rcases cell with cf | rectangle
    · fin_cases corner
      · refine ⟨(0, bits.2), ?_⟩
        simpa [rxLocalCellBoundaryEdge, rxFaceQ, localFaceQAt,
          localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt] using hfaceQ
      · refine ⟨(1, bits.1), ?_⟩
        simpa [rxLocalCellBoundaryEdge, rxFaceQ, localFaceQAt,
          localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt] using hfaceQ
    · fin_cases corner
      · refine ⟨(0, bits.1), ?_⟩
        simpa [rxLocalCellBoundaryEdge, rxFaceQ, localFaceQAt,
          localFaceQ0, localFaceQ0Edge, localFaceQ0EdgeAt] using hfaceQ
      · refine ⟨(1, bits.2), ?_⟩
        simpa [rxLocalCellBoundaryEdge, rxFaceQ, localFaceQAt,
          localFaceQ1, localFaceQ1Edge, localFaceQ1EdgeAt] using hfaceQ
  · cases hfaceZ
  · cases hfaceZ
private theorem zDegree_rx_qEdge_le (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    zDegree (rxReplacementPresentation P S) (Sum.inl (Sum.inr ⟨q, edge⟩)) ≤
      qXDegree P q + 2 := by
  classical
  change _ ≤ Fintype.card {x : P.X // P.xq x q = true} + 2
  rw [← Fintype.card_fin 2, ← Fintype.card_sum]
  apply card_fiber_le_of_covered _ (rxQEdgeNeighbour P S q edge)
  intro vertex hv
  obtain ⟨face, corner, hq, hz⟩ :=
    (rxQZIncidence_eq_true_iff P S vertex (Sum.inl (Sum.inr ⟨q, edge⟩))).1 hv
  rcases face with localFace | ⟨oldXQ, oldEdge, endpoint⟩ | old
  · cases hz
  · have htag : (⟨oldXQ.1.2, oldEdge⟩ : Σ q : P.Q, QDoubleCylinderEdge P q S) =
        ⟨q, edge⟩ := Sum.inr.inj (Sum.inl.inj hz)
    cases htag
    fin_cases corner
    · refine ⟨Sum.inl ⟨oldXQ.1.1, oldXQ.2⟩, ?_⟩
      exact hq
    · refine ⟨Sum.inr endpoint, ?_⟩
      exact hq
  · cases hz
private theorem zDegree_rx_old_le (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (copy : Fin 2) :
    zDegree (rxReplacementPresentation P S) (Sum.inr (z, copy)) ≤ zDegree P z := by
  classical
  apply card_fiber_le_of_covered _ (fun q : {q : P.Q // P.qz q z = true} =>
    (Sum.inr ⟨q.1, (copy, Sum.inl (Sum.inr (⟨z, q.2⟩ : QStarEdge P q.1)))⟩ : RX1 P S))
  intro vertex hv
  obtain ⟨face, corner, hq, hz⟩ :=
    (rxQZIncidence_eq_true_iff P S vertex (Sum.inr (z, copy))).1 hv
  rcases face with localFace | glue | ⟨oldFace, oldCopy⟩
  · cases hz
  · cases hz
  · have hz' : P.faceZ oldFace = z ∧ oldCopy = copy :=
      Prod.mk.inj (Sum.inr.inj hz)
    obtain ⟨hz', rfl⟩ := hz'
    refine ⟨⟨P.faceQ oldFace corner, by
      simpa [hz'] using P.data.faceQ_qz oldFace corner⟩, ?_⟩
    simpa [rxFaceQ, oldZFaceQ, hz'] using hq
private theorem rx_z_bounded (P : TannerSquarePresentation) (S : OddScale)
    (h : BoundedValence P) (z : RX2 P S) :
    zDegree (rxReplacementPresentation P S) z ≤ 7 := by
  rcases z with (⟨x, cell⟩ | ⟨q, edge⟩) | ⟨oldZ, copy⟩
  · exact (zDegree_rx_local_le_four P S x cell).trans (by decide)
  · have hz := zDegree_rx_qEdge_le P S q edge
    have hx := (h.2.2 q).1
    omega
  · exact (zDegree_rx_old_le P S oldZ copy).trans (h.2.1 oldZ)
private theorem xq_boundary (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    xStarBoundaryVertexMember P x (Vertex.q q) = true := by
  let z := A.qzRoot q
  let shared : SharedQ P.data x z.1 := ⟨q, by simp [hxq, z.2]⟩
  obtain ⟨⟨face, corner⟩, hc⟩ := (P.perfectPairing x z.1).2 shared
  have hq : P.faceQ face.1 corner = q := congrArg Subtype.val hc
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
  refine ⟨face.1, by simpa [xStarFaceMember] using face.2.1, ?_⟩
  fin_cases corner
  · exact Or.inl hq.symm
  · exact Or.inr hq.symm
private theorem xDegree_rx_central_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X) (copy : Fin 2) :
    xDegree (rxReplacementPresentation P S) (rxOriginalCentralXCoordinate P S x copy) ≤
      xDegree P x := by
  classical
  apply card_fiber_le_of_covered _ (fun q : {q : P.Q // P.xq x q = true} =>
    rxOriginalCentralQCoordinate P S x copy q.1 (xq_boundary P A x q.1 q.2))
  intro q hq
  obtain ⟨candidate, corner, hx, hc⟩ :=
    (rxXQIncidence_eq_true_iff P S (rxOriginalCentralXCoordinate P S x copy) q).1 hq
  obtain ⟨face, rfl⟩ := rxOriginalCentralFace_cases P S x copy candidate hx
  have hfaceX : P.faceX face.1 = x := by simpa [xStarFaceMember] using face.2
  have hinc : P.xq x (P.faceQ face.1 corner) = true := by
    simpa [hfaceX] using P.data.faceQ_xq face.1 corner
  refine ⟨⟨P.faceQ face.1 corner, hinc⟩, ?_⟩
  exact (rxOriginalCentralFace_qCoordinate P S x copy face corner).symm.trans hc
private theorem rx_xq_boundary (P : TannerSquarePresentation) (S : OddScale)
    (x : RX0 P S) (q : RX1 P S) (h : rxXQIncidence P S x q = true) :
    xStarBoundaryVertexMember (rxReplacementPresentation P S) x (Vertex.q q) = true := by
  classical
  obtain ⟨face, corner, hx, hq⟩ := (rxXQIncidence_eq_true_iff P S x q).1 h
  simp only [xStarBoundaryVertexMember, decide_eq_true_eq]
  refine ⟨face, ?_, ?_⟩
  · unfold xStarFaceMember
    apply decide_eq_true
    exact hx
  · fin_cases corner
    · exact Or.inl hq.symm
    · exact Or.inr hq.symm
private theorem xDegree_rx_originalQ_le (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : P.X) (copy : Fin 2)
    (q : P.Q) (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    xDegree (rxReplacementPresentation P S)
      (rxOriginalBoundaryQXCoordinate P S x copy q member) ≤ qZDegree P q + 3 := by
  classical
  change _ ≤ Fintype.card (QStarEdge P q) + 3
  rw [← Fintype.card_fin 3, ← Fintype.card_sum]
  apply card_fiber_le_of_covered
    (fun target : RX1 P S => rxXQIncidence P S
      (rxOriginalBoundaryQXCoordinate P S x copy q member) target = true)
    (rxOriginalBoundaryQNeighbour P A4 S x copy q member)
  intro target h
  exact rxOriginalBoundaryQNeighbour_covers P A4 S x copy q member target
    (rx_xq_boundary P S _ target h)
private theorem xDegree_rx_originalZ_le_five (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Fin 2) (z : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z z) = true) :
    xDegree (rxReplacementPresentation P S)
      (rxOriginalBoundaryZXCoordinate P S x copy z member) ≤ 5 := by
  classical
  have hcover := card_fiber_le_of_covered
    (fun q : RX1 P S => rxXQIncidence P S
      (rxOriginalBoundaryZXCoordinate P S x copy z member) q = true)
    (rxOriginalBoundaryZNeighbour P A4 S x copy z member)
    (fun q h => rxOriginalBoundaryZNeighbour_covers P R A4 S x copy z member q
      (rx_xq_boundary P S _ q h))
  have hshared := sharedQ_card_le_two P R x z
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit] at hcover
  exact hcover.trans (by omega)
private theorem radialFaceCorner_card_le (P : TannerSquarePresentation) (x : P.X)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true) :
    Fintype.card (RXRadialFaceCorner P x radial member) ≤ qZDegree P radial.1.2 := by
  classical
  let route : RXRadialFaceCorner P x radial member → XQIncidentFace P radial := fun fc =>
    ⟨fc.1.1.1, by
      have he : faceXQEdge P fc.1.1.1 fc.1.2 = radial :=
        Sum.inl.inj (congrArg Subtype.val fc.2)
      exact ⟨congrArg (fun e => e.1.1) he,
        fc.1.2, congrArg (fun e => e.1.2) he⟩⟩
  rw [← xqIncidentFace_card]
  apply Fintype.card_le_of_injective route
  intro a b h
  have hf : a.1.1.1 = b.1.1.1 := by
    simpa only [route] using congrArg (fun f : XQIncidentFace P radial => f.1) h
  have ha : P.faceQ a.1.1.1 a.1.2 = radial.1.2 :=
    congrArg (fun e : XStarEdge P x =>
      match e.1 with | Sum.inl v => v.1.2 | Sum.inr _ => radial.1.2) a.2
  have hb : P.faceQ b.1.1.1 b.1.2 = radial.1.2 :=
    congrArg (fun e : XStarEdge P x =>
      match e.1 with | Sum.inl v => v.1.2 | Sum.inr _ => radial.1.2) b.2
  have hc : a.1.2 = b.1.2 := P.faceQ_injective a.1.1.1 (ha.trans (hf.symm ▸ hb).symm)
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hf) hc
private theorem xDegree_rx_radialInterior_le (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (x : P.X) (copy : Fin 2)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (index : Fin (S.half - 1)) :
    xDegree (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inl (⟨Sum.inl radial, member⟩, index)))⟩ ≤
      qZDegree P radial.1.2 + 2 := by
  classical
  have hcover := card_fiber_le_of_covered
    (fun q : RX1 P S => rxXQIncidence P S
      ⟨x, (copy, Sum.inr (Sum.inl (⟨Sum.inl radial, member⟩, index)))⟩ q = true)
    (rxRadialInteriorNeighbour P S x copy radial member index)
    (fun q h => rxRadialInteriorNeighbour_covers P A4 S x copy radial member index q h)
  simp only [Fintype.card_sum, Fintype.card_fin] at hcover
  exact hcover.trans (Nat.add_le_add_right (radialFaceCorner_card_le P x radial member) 2)
private theorem boundaryFaceCorner_card_le_one (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) (x : P.X) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true) :
    Fintype.card (RXBoundaryFaceCorner P x edge member) ≤ 1 := by
  classical
  apply Fintype.card_le_one_iff_subsingleton.mpr
  constructor
  intro a b
  have ha : faceQZEdge P a.1.1.1 a.1.2 = edge :=
    Sum.inr.inj (congrArg Subtype.val a.2)
  have hb : faceQZEdge P b.1.1.1 b.1.2 = edge :=
    Sum.inr.inj (congrArg Subtype.val b.2)
  have hax : P.faceX a.1.1.1 = x := by simpa [xStarFaceMember] using a.1.1.2
  have hbx : P.faceX b.1.1.1 = x := by simpa [xStarFaceMember] using b.1.1.2
  have haz : P.faceZ a.1.1.1 = edge.1.2 := congrArg (fun e => e.1.2) ha
  have hbz : P.faceZ b.1.1.1 = edge.1.2 := congrArg (fun e => e.1.2) hb
  have hf : a.1.1.1 = b.1.1.1 :=
    R.faceXZ_injective (Prod.ext (hax.trans hbx.symm) (haz.trans hbz.symm))
  have haq : P.faceQ a.1.1.1 a.1.2 = edge.1.1 := congrArg (fun e => e.1.1) ha
  have hbq : P.faceQ b.1.1.1 b.1.2 = edge.1.1 := congrArg (fun e => e.1.1) hb
  have hc : a.1.2 = b.1.2 :=
    P.faceQ_injective a.1.1.1 (haq.trans (hf.symm ▸ hbq).symm)
  exact Subtype.ext (Prod.ext (Subtype.ext hf) hc)
private theorem rxStarEdgeInteriorRectangleQ1_eq
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Fin 2)
    (edge : QZEdge P) (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    localFaceQAt P S
      (rxStarEdgeInteriorRectangleBeforeLocalFace P S x copy edge member index) 1 =
    localFaceQAt P S
      (rxStarEdgeInteriorRectangleAfterLocalFace P S x copy edge member index) 1 := by
  have hnotlast : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [rxStarEdgeInteriorRectangleBeforeLocalFace,
    rxStarEdgeInteriorRectangleAfterLocalFace,
    rxStarEdgeInteriorRectangleBefore, rxStarEdgeInteriorRectangleAfter,
    subdivisionOriginalBoundaryEdge, localFaceQAt, localFaceQ1,
    localFaceQ1Edge, localFaceQ1EdgeAt, doubleCylinderRectangleBoundaryEdge,
    subdivisionBoundaryEdgeStart, subdivisionBoundaryEdgeEnd,
    subdivisionEdgeStart, subdivisionEdgeEnd, subdivisionSegmentStart,
    subdivisionSegmentEnd, rxStarEdgeInteriorPreviousIndex,
    rxStarEdgeInteriorNextIndex, hnotlast]
private theorem rxStarEdgeInteriorGlueQ1_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Fin 2) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    glueFaceQ1 P S (rxStarEdgeInteriorGlueBefore P A4 S x copy edge member index) =
    glueFaceQ1 P S (rxStarEdgeInteriorGlueAfter P A4 S x copy edge member index) := by
  have hnotlast : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [rxStarEdgeInteriorGlueBefore, rxStarEdgeInteriorGlueAfter,
    glueFaceQ1, edgeEndpoint, qDoubleCylinderEdgeStart, qDoubleCylinderEdgeEnd,
    qSubdivisionEdgeStart, qSubdivisionEdgeEnd,
    rxStarEdgeInteriorPreviousIndex, rxStarEdgeInteriorNextIndex, hnotlast]
private theorem rxBoundaryInteriorNeighbour_covers
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) (target : RX1 P S)
    (h : rxXQIncidence P S
      ⟨x, (copy, Sum.inr (Sum.inl (⟨Sum.inr edge, member⟩, index)))⟩ target = true) :
    ∃ tag, rxBoundaryInteriorNeighbour P A4 S x copy edge member index tag = target := by
  obtain ⟨candidate, qCorner, hx, hq⟩ := (rxXQIncidence_eq_true_iff P S _ target).1 h
  have cases := rxStarEdgeInteriorIncidentFace_cases P A4 S x copy
    ⟨Sum.inr edge, member⟩ index candidate hx
  rcases cases with ⟨face, corner, hedge, hbefore | hafter⟩ |
    ⟨boundary, boundaryMember, hboundary, houter⟩
  · subst candidate
    by_cases halong : qCorner = rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩ corner
    · refine ⟨Sum.inr 0, ?_⟩
      have ha := rxStarEdgeInteriorBeforeAlongQAt P S x copy
        ⟨Sum.inr edge, member⟩ index face corner hedge
      simpa [rxBoundaryInteriorNeighbour] using
        ha.symm.trans (by simpa [rxFaceQ, localFaceQAt, halong] using hq)
    · have hacross : qCorner =
          rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inr edge, member⟩ corner := by
        fin_cases qCorner <;> fin_cases corner <;>
          simp [rxStarEdgeInteriorAlongCornerAt, rxStarEdgeInteriorAcrossCornerAt,
            rxTwoElim] at halong ⊢
      exact ⟨Sum.inl ⟨(face, corner), hedge⟩,
        by simpa [rxBoundaryInteriorNeighbour, rxFaceQ, localFaceQAt, hacross] using hq⟩
  · subst candidate
    by_cases halong : qCorner = rxStarEdgeInteriorAlongCornerAt ⟨Sum.inr edge, member⟩ corner
    · refine ⟨Sum.inr 1, ?_⟩
      have ha := rxStarEdgeInteriorAfterAlongQAt P S x copy
        ⟨Sum.inr edge, member⟩ index face corner hedge
      simpa [rxBoundaryInteriorNeighbour] using
        ha.symm.trans (by simpa [rxFaceQ, localFaceQAt, halong] using hq)
    · have hacross : qCorner =
          rxStarEdgeInteriorAcrossCornerAt ⟨Sum.inr edge, member⟩ corner := by
        fin_cases qCorner <;> fin_cases corner <;>
          simp [rxStarEdgeInteriorAlongCornerAt, rxStarEdgeInteriorAcrossCornerAt,
            rxTwoElim] at halong ⊢
      refine ⟨Sum.inl ⟨(face, corner), hedge⟩, ?_⟩
      exact (rxStarEdgeInteriorAcrossQAt P S x copy
        ⟨Sum.inr edge, member⟩ index face corner).trans
        (by simpa [rxFaceQ, localFaceQAt, hacross] using hq)
  · have he : edge = boundary := Sum.inr.inj (congrArg Subtype.val hboundary)
    subst boundary
    have cases := rxStarEdgeInteriorOuterQ_cases P A4 S x copy edge member index
      candidate qCorner houter
    rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · refine ⟨Sum.inr 0, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorRectangleBeforeQ0 P S x copy edge member index).symm.trans
          (h0.symm.trans hq)
    · exact ⟨Sum.inr 2, by simpa [rxBoundaryInteriorNeighbour] using h1.symm.trans hq⟩
    · refine ⟨Sum.inr 1, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorRectangleAfterQ0 P S x copy edge member index).symm.trans
          (h2.symm.trans hq)
    · refine ⟨Sum.inr 2, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorRectangleQ1_eq P S x copy edge member index).trans
          (h3.symm.trans hq)
    · refine ⟨Sum.inr 0, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorGlueBeforeQ0 P A4 S x copy edge member index).symm.trans
          (h4.symm.trans hq)
    · exact ⟨Sum.inr 3, by simpa [rxBoundaryInteriorNeighbour] using h5.symm.trans hq⟩
    · refine ⟨Sum.inr 1, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorGlueAfterQ0 P A4 S x copy edge member index).symm.trans
          (h6.symm.trans hq)
    · refine ⟨Sum.inr 3, ?_⟩
      simpa [rxBoundaryInteriorNeighbour] using
        (rxStarEdgeInteriorGlueQ1_eq P A4 S x copy edge member index).trans
          (h7.symm.trans hq)
private theorem xDegree_rx_boundaryInterior_le_five (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (copy : Fin 2) (edge : QZEdge P)
    (member : xStarEdgeMember P x (Sum.inr edge) = true)
    (index : Fin (S.half - 1)) :
    xDegree (rxReplacementPresentation P S)
      ⟨x, (copy, Sum.inr (Sum.inl (⟨Sum.inr edge, member⟩, index)))⟩ ≤ 5 := by
  classical
  have hcard := card_fiber_le_of_covered _
    (rxBoundaryInteriorNeighbour P A4 S x copy edge member index)
    (rxBoundaryInteriorNeighbour_covers P A4 S x copy edge member index)
  have hone := boundaryFaceCorner_card_le_one P R x edge member
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact hcard.trans (by omega)
private theorem rx_x_bounded (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (hB : BoundedValence P) (vertex : RX0 P S) :
    xDegree (rxReplacementPresentation P S) vertex ≤ 7 := by
  rcases vertex with ⟨x, copy, old | (⟨edge, index⟩ | ⟨face, i, j⟩)⟩
  · rcases old with ⟨oldX | oldQ | oldZ, member⟩
    · have hx : oldX = x := by simpa [xStarVertexMember] using member
      subst oldX
      exact (xDegree_rx_central_le P A4.toTannerSquareAdmissibleV3.toTannerSquareAdmissible
        S x copy).trans (hB.1 x)
    · have boundary : xStarBoundaryVertexMember P x (Vertex.q oldQ) = true := by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member
      have h := xDegree_rx_originalQ_le P A4 S x copy oldQ boundary
      have hb := (hB.2.2 oldQ).2.1
      exact h.trans (by omega)
    · have boundary : xStarBoundaryVertexMember P x (Vertex.z oldZ) = true := by
        simpa [xStarBoundaryVertexMember, xStarVertexMember] using member
      exact (xDegree_rx_originalZ_le_five P R A4 S x copy oldZ boundary).trans (by decide)
  · rcases edge with ⟨radial | boundary, member⟩
    · have h := xDegree_rx_radialInterior_le P A4 S x copy radial member index
      have hb := (hB.2.2 radial.1.2).2.1
      exact h.trans (by omega)
    · exact (xDegree_rx_boundaryInterior_le_five P A4 R S x copy boundary member index).trans
        (by decide)
  · exact (rxFaceInterior_xq_card_le_four P S x copy face i j).trans (by decide)
private theorem rx_local_z_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : DoubleCylinderEdge P x S) (z : RX2 P S)
    (h : rxQZIncidence P S (Sum.inl ⟨x, edge⟩) z = true) :
    (∃ copy : Two, ∃ face : SubdivisionFace P x S, ∃ slot : Two × Two,
      edge = Sum.inl (copy, subdivisionFaceBoundaryEdge P x S face slot) ∧
      z = Sum.inl (Sum.inl ⟨x, Sum.inl (copy, face)⟩)) ∨
    (∃ rectangle : SubdivisionBoundaryEdge P x S, ∃ slot : Two × Two,
      edge = doubleCylinderRectangleBoundaryEdge P x S rectangle slot ∧
      z = Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩)) ∨
    (∃ q : P.Q, ∃ hxq : P.xq x q = true,
      ∃ qEdge : QDoubleCylinderEdge P q S,
      edge = qToXDoubleCylinderEdgeRaw P q x hxq S qEdge ∧
      z = Sum.inl (Sum.inr ⟨q, qEdge⟩)) := by
  obtain ⟨face, corner, hq, hz⟩ :=
    (rxQZIncidence_eq_true_iff P S (Sum.inl ⟨x, edge⟩) z).1 h
  rcases face with localFace | glue | old
  · rcases localFace with ⟨oldX, cell, material⟩
    have htag : oldX = x := by
      fin_cases corner <;>
        exact congrArg Sigma.fst (Sum.inl.inj hq)
    subst oldX
    rcases cell with ⟨copy, small⟩ | rectangle
    · left
      refine ⟨copy, small, ?_⟩
      fin_cases corner
      · refine ⟨(0, material.2), ?_, hz.symm⟩
        exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2).symm
      · refine ⟨(1, material.1), ?_, hz.symm⟩
        exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2).symm
    · right; left
      refine ⟨rectangle, ?_⟩
      fin_cases corner
      · refine ⟨(0, material.1), ?_, hz.symm⟩
        exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2).symm
      · refine ⟨(1, material.2), ?_, hz.symm⟩
        exact (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2).symm
  · rcases glue with ⟨a, qEdge, endpoint⟩
    fin_cases corner
    · have htag : a.1.1 = x := congrArg Sigma.fst (Sum.inl.inj hq)
      subst x
      exact Or.inr (Or.inr ⟨a.1.2, a.2, qEdge,
        (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2).symm, hz.symm⟩)
    · cases hq
  · cases hq
private theorem rx_local_z_face_at_endpoint
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : DoubleCylinderEdge P x S) (z : RX2 P S) (endpoint : Two)
    (h : rxQZIncidence P S (Sum.inl ⟨x, edge⟩) z = true) :
    ∃ face : RXFace P S, ∃ corner : Two,
      rxFaceX P S face = ⟨x, edgeEndpoint
        (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S) edge endpoint⟩ ∧
      rxFaceQ P S face corner = Sum.inl ⟨x, edge⟩ ∧
      rxFaceZ P S face = z := by
  obtain ⟨face, corner, hq, hz⟩ :=
    (rxQZIncidence_eq_true_iff P S (Sum.inl ⟨x, edge⟩) z).1 h
  rcases face with localFace | glue | old
  · rcases localFace with ⟨oldX, cell, material⟩
    have htag : oldX = x := by
      fin_cases corner <;> exact congrArg Sigma.fst (Sum.inl.inj hq)
    subst oldX
    let nextMaterial := localMaterialCornerAtEndpoint P x S cell material corner endpoint
    refine ⟨Sum.inl ⟨x, cell, nextMaterial⟩, corner, ?_, ?_, hz⟩
    · have he : (if corner = 0 then localFaceQ0EdgeAt P x S cell material
          else localFaceQ1EdgeAt P x S cell material) = edge := by
        fin_cases corner <;>
          exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2
      exact (localFaceX_atEndpoint P x S cell material corner endpoint).trans
        (by rw [he])
    · exact (localFaceQ_atEndpoint P x S cell material corner endpoint).trans hq
  · rcases glue with ⟨a, qEdge, originalEndpoint⟩
    fin_cases corner
    · have htag : a.1.1 = x := congrArg Sigma.fst (Sum.inl.inj hq)
      subst x
      have he : qToXDoubleCylinderEdgeRaw P a.1.2 a.1.1 a.2 S qEdge = edge :=
        eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj hq)).2
      refine ⟨Sum.inr (Sum.inl ⟨a, qEdge, endpoint⟩), 0, ?_, hq, hz⟩
      exact congrArg (fun e : DoubleCylinderEdge P a.1.1 S =>
        (⟨a.1.1, edgeEndpoint (tannerDoubleCylinderEdgeStart P a.1.1 S)
          (tannerDoubleCylinderEdgeEnd P a.1.1 S) e endpoint⟩ : RX0 P S)) he
    · cases hq
  · cases hq
private theorem qZDegree_rx_local_le_four_of_interior_endpoint
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (edge : DoubleCylinderEdge P x S) (endpoint copy : Two)
    (face : XStarFace P x) (i j : Fin (S.half - 1))
    (he : edgeEndpoint (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S) edge endpoint =
      (copy, Sum.inr (Sum.inr (face, i, j)))) :
    qZDegree (rxReplacementPresentation P S) (Sum.inl ⟨x, edge⟩) ≤ 4 := by
  classical
  let a := rxFaceZ P S (Sum.inl (rxFaceInteriorLocalFaceSW P S x copy face i j))
  let b := rxFaceZ P S (Sum.inl (rxFaceInteriorLocalFaceSE P S x copy face i j))
  let c := rxFaceZ P S (Sum.inl (rxFaceInteriorLocalFaceNW P S x copy face i j))
  let d := rxFaceZ P S (Sum.inl (rxFaceInteriorLocalFaceNE P S x copy face i j))
  have cover : ∀ z, rxQZIncidence P S (Sum.inl ⟨x, edge⟩) z = true →
      z ∈ ({a, b, c, d} : Finset (RX2 P S)) := by
    intro z hz
    obtain ⟨candidate, corner, hx, _, hZ⟩ :=
      rx_local_z_face_at_endpoint P S x edge z endpoint hz
    rw [he] at hx
    have cases := rxFaceInteriorFace_cases P S x copy face i j candidate hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases cases with h | h | h | h
    · exact Or.inl (hZ.symm.trans (congrArg (rxFaceZ P S) h))
    · exact Or.inr (Or.inl (hZ.symm.trans (congrArg (rxFaceZ P S) h)))
    · exact Or.inr (Or.inr (Or.inl (hZ.symm.trans (congrArg (rxFaceZ P S) h))))
    · exact Or.inr (Or.inr (Or.inr (hZ.symm.trans (congrArg (rxFaceZ P S) h))))
  calc
    _ = (Finset.univ.filter (fun z =>
        rxQZIncidence P S (Sum.inl ⟨x, edge⟩) z = true)).card :=
      Fintype.card_subtype _
    _ ≤ ({a, b, c, d} : Finset (RX2 P S)).card := by
      apply Finset.card_le_card
      intro z hz
      exact cover z (Finset.mem_filter.mp hz).2
    _ ≤ 4 := Finset.card_le_four
private theorem qZDegree_rx_horizontal_le_four
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i : Fin S.half) (j : Fin (S.half - 1)) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inr (Sum.inl (face, i, j)))⟩) ≤ 4 := by
  have hj0 : j.1 + 1 ≠ 0 := by omega
  have hjlast : j.1 + 1 ≠ S.half := by have := j.2; omega
  by_cases hi : i.1 = 0
  · have hm : 1 < S.half := by have := j.2; omega
    apply qZDegree_rx_local_le_four_of_interior_endpoint P S x _ 1 copy face
      ⟨0, by omega⟩ j
    change (copy, subdivisionGridVertex P x S face
      ⟨i.1 + 1, _⟩ ⟨j.1 + 1, _⟩) = _
    simp [subdivisionGridVertex, hi, hj0, hjlast, ne_of_lt hm]
    constructor
    · apply Fin.ext
      change 1 - 1 = 0
      omega
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
  · let k : Fin (S.half - 1) := ⟨i.1 - 1, by have := i.2; omega⟩
    apply qZDegree_rx_local_le_four_of_interior_endpoint P S x _ 0 copy face k j
    change (copy, subdivisionGridVertex P x S face
      ⟨i.1, _⟩ ⟨j.1 + 1, _⟩) = _
    simp [subdivisionGridVertex, hi, ne_of_lt i.2, hj0, hjlast, k]
    constructor
    · apply Fin.ext
      change i.1 - 1 = i.1 - 1
      rfl
    · apply Fin.ext
      change (j.1 + 1) - 1 = j.1
      omega
private theorem qZDegree_rx_vertical_grid_le_four
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (copy : Two) (face : XStarFace P x)
    (i : Fin (S.half - 1)) (j : Fin S.half) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inr (Sum.inr (face, i, j)))⟩) ≤ 4 := by
  have hi0 : i.1 + 1 ≠ 0 := by omega
  have hilast : i.1 + 1 ≠ S.half := by have := i.2; omega
  by_cases hj : j.1 = 0
  · have hm : 1 < S.half := by have := i.2; omega
    apply qZDegree_rx_local_le_four_of_interior_endpoint P S x _ 1 copy face
      i ⟨0, by omega⟩
    change (copy, subdivisionGridVertex P x S face
      ⟨i.1 + 1, _⟩ ⟨j.1 + 1, _⟩) = _
    simp [subdivisionGridVertex, hj, hi0, hilast, ne_of_lt hm]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change 1 - 1 = 0
      omega
  · let k : Fin (S.half - 1) := ⟨j.1 - 1, by have := j.2; omega⟩
    apply qZDegree_rx_local_le_four_of_interior_endpoint P S x _ 0 copy face i k
    change (copy, subdivisionGridVertex P x S face
      ⟨i.1 + 1, _⟩ ⟨j.1, _⟩) = _
    simp [subdivisionGridVertex, hj, ne_of_lt j.2, hi0, hilast, k]
    constructor
    · apply Fin.ext
      change (i.1 + 1) - 1 = i.1
      omega
    · apply Fin.ext
      change j.1 - 1 = j.1 - 1
      rfl
private theorem qZDegree_rx_vertical_oldQ_le
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (q : P.Q)
    (member : xStarBoundaryVertexMember P x (Vertex.q q) = true) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inr (subdivisionOriginalBoundaryVertex P x S
        ⟨Vertex.q q, member⟩)⟩) ≤ qZDegree P q := by
  classical
  let hxq := rxOriginalXBoundaryQ_incidence P x q member
  let neighbour : QStarEdge P q → RX2 P S := fun z =>
    Sum.inl (Sum.inl ⟨x, Sum.inr
      (qToXSubdivisionBoundaryEdge P q x hxq S (z, ⟨0, S.half_pos⟩))⟩)
  apply card_fiber_le_of_covered
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inr (subdivisionOriginalBoundaryVertex P x S
        ⟨Vertex.q q, member⟩)⟩) z = true) neighbour
  intro z hz
  rcases rx_local_z_cases P S x _ z hz with hsmall | hrect | hglue
  · obtain ⟨copy, face, slot, he, _⟩ := hsmall
    cases he
  · obtain ⟨rectangle, ⟨axis, side⟩, he, hz⟩ := hrect
    fin_cases axis
    · simp [doubleCylinderRectangleBoundaryEdge] at he
    · rcases rectangle with ⟨raw, hboundary⟩
      rcases raw with ⟨⟨raw, hstar⟩, k⟩ | interior
      · rcases raw with radial | qe
        · simp [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember] at hboundary
        · fin_cases side
          · have hv := congrArg Subtype.val (Sum.inr.inj he)
            rw [subdivisionBoundaryEdgeStart_value] at hv
            change Sum.inl (⟨Vertex.q q, _⟩ : XStarVertex P x) =
              subdivisionSegmentStart P x S ⟨Sum.inr qe, hstar⟩ k at hv
            by_cases hk : k.1 = 0
            · rw [subdivisionSegmentStart, dif_pos hk] at hv
              have hq : q = qe.1.1 :=
                Vertex.q.inj (congrArg Subtype.val (Sum.inl.inj hv))
              let oldZ : QStarEdge P q := ⟨qe.1.2, by simpa [hq] using qe.2⟩
              refine ⟨oldZ, ?_⟩
              rw [hz]
              have hk' : k = (⟨0, S.half_pos⟩ : Fin S.half) := Fin.ext hk
              subst k
              simp [neighbour, qToXSubdivisionBoundaryEdge,
                subdivisionOriginalBoundaryEdge, qToXBoundaryEdge, xStarBoundaryEdgeToStar, oldZ, hq]
            · simp [subdivisionSegmentStart, hk] at hv
          · have hv := congrArg Subtype.val (Sum.inr.inj he)
            rw [subdivisionBoundaryEdgeEnd_value] at hv
            change Sum.inl (⟨Vertex.q q, _⟩ : XStarVertex P x) =
              subdivisionSegmentEnd P x S ⟨Sum.inr qe, hstar⟩ k at hv
            by_cases hk : k.1 + 1 = S.half
            · rw [subdivisionSegmentEnd, dif_pos hk] at hv
              have impossible := congrArg Subtype.val (Sum.inl.inj hv)
              cases impossible
            · simp [subdivisionSegmentEnd, hk] at hv
      · simp [subdivisionBoundaryEdgeMember] at hboundary
  · obtain ⟨oldQ, oldIncidence, qEdge, he, _⟩ := hglue
    rcases qEdge with endEdge | endpoint
    · cases he
    · have hv := congrArg Subtype.val (Sum.inr.inj he)
      have impossible := congrArg Subtype.val (Sum.inl.inj hv)
      cases impossible
private theorem qZDegree_rx_vertical_oldZ_le_four
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (oldZ : P.Z)
    (member : xStarBoundaryVertexMember P x (Vertex.z oldZ) = true) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inr (subdivisionOriginalBoundaryVertex P x S
        ⟨Vertex.z oldZ, member⟩)⟩) ≤ 4 := by
  classical
  have cover : ∀ z, rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inr (subdivisionOriginalBoundaryVertex P x S
        ⟨Vertex.z oldZ, member⟩)⟩) z = true →
      ∃ tag, rxVerticalOldZZNeighbour P S x oldZ tag = z := by
    intro z hz
    rcases rx_local_z_cases P S x _ z hz with hsmall | hrect | hglue
    · obtain ⟨copy, face, slot, he, _⟩ := hsmall
      cases he
    · obtain ⟨rectangle, ⟨axis, side⟩, he, hz⟩ := hrect
      fin_cases axis
      · simp [doubleCylinderRectangleBoundaryEdge] at he
      · rcases rectangle with ⟨raw, hboundary⟩
        rcases raw with ⟨⟨raw, hstar⟩, k⟩ | interior
        · rcases raw with radial | qe
          · simp [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember] at hboundary
          · fin_cases side
            · have hv := congrArg Subtype.val (Sum.inr.inj he)
              rw [subdivisionBoundaryEdgeStart_value] at hv
              change Sum.inl (⟨Vertex.z oldZ, _⟩ : XStarVertex P x) =
                subdivisionSegmentStart P x S ⟨Sum.inr qe, hstar⟩ k at hv
              by_cases hk : k.1 = 0
              · rw [subdivisionSegmentStart, dif_pos hk] at hv
                have impossible := congrArg Subtype.val (Sum.inl.inj hv)
                cases impossible
              · simp [subdivisionSegmentStart, hk] at hv
            · have hv := congrArg Subtype.val (Sum.inr.inj he)
              rw [subdivisionBoundaryEdgeEnd_value] at hv
              change Sum.inl (⟨Vertex.z oldZ, _⟩ : XStarVertex P x) =
                subdivisionSegmentEnd P x S ⟨Sum.inr qe, hstar⟩ k at hv
              by_cases hk : k.1 + 1 = S.half
              · rw [subdivisionSegmentEnd, dif_pos hk] at hv
                have hez : oldZ = qe.1.2 :=
                  Vertex.z.inj (congrArg Subtype.val (Sum.inl.inj hv))
                let shared : SharedQ P.data x oldZ :=
                  ⟨qe.1.1, by simp [xStarQZEdge_xq P x qe hstar, hez, qe.2]⟩
                refine ⟨(shared, 0), ?_⟩
                rw [hz]
                have hk' : k = rxStarEdgeInteriorLastIndex S := by
                  apply Fin.ext
                  change k.1 = S.half - 1
                  omega
                subst k
                simp [rxVerticalOldZZNeighbour, shared, qToXSubdivisionBoundaryEdge,
                  subdivisionOriginalBoundaryEdge, qToXBoundaryEdge, xStarBoundaryEdgeToStar,
                  rxStarEdgeInteriorLastIndex, hez]
              · simp [subdivisionSegmentEnd, hk] at hv
        · simp [subdivisionBoundaryEdgeMember] at hboundary
    · obtain ⟨q, hxq, qEdge, he, hz⟩ := hglue
      rcases qEdge with endEdge | endpoint
      · cases he
      · have hv := congrArg Subtype.val (Sum.inr.inj he)
        have hez : oldZ = endpoint.1 :=
          Vertex.z.inj (congrArg Subtype.val (Sum.inl.inj hv))
        let shared : SharedQ P.data x oldZ :=
          ⟨q, by simp [hxq, hez, endpoint.2]⟩
        refine ⟨(shared, 1), ?_⟩
        rw [hz]
        simp [rxVerticalOldZZNeighbour, shared, hez]
  calc
    _ ≤ Fintype.card (SharedQ P.data x oldZ × Two) :=
      card_fiber_le_of_covered
        (fun z : RX2 P S => rxQZIncidence P S
          (Sum.inl ⟨x, Sum.inr (subdivisionOriginalBoundaryVertex P x S
            ⟨Vertex.z oldZ, member⟩)⟩) z = true)
        (rxVerticalOldZZNeighbour P S x oldZ) cover
    _ = Fintype.card (SharedQ P.data x oldZ) * 2 := by simp [Fintype.card_prod]
    _ ≤ 4 := by have := sharedQ_card_le_two P R x oldZ; omega
private theorem qZDegree_rx_vertical_boundaryInterior_le_two
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (oldEdge : XStarEdge P x) (index : Fin (S.half - 1))
    (member : xStarBoundaryEdgeMember P x oldEdge.1 = true) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inr
        ⟨Sum.inr (Sum.inl (oldEdge, index)), member⟩⟩) ≤ 2 := by
  classical
  let previous : Fin S.half := ⟨index.1, by have := index.2; omega⟩
  let next : Fin S.half := ⟨index.1 + 1, by have := index.2; omega⟩
  let rectangle (k : Fin S.half) : SubdivisionBoundaryEdge P x S :=
    ⟨Sum.inl (oldEdge, k), member⟩
  let zOf (r : SubdivisionBoundaryEdge P x S) : RX2 P S :=
    Sum.inl (Sum.inl ⟨x, Sum.inr r⟩)
  apply card_fiber_le_two
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inr
        ⟨Sum.inr (Sum.inl (oldEdge, index)), member⟩⟩) z = true)
    (zOf (rectangle previous)) (zOf (rectangle next))
  intro z hz
  rcases rx_local_z_cases P S x _ z hz with hsmall | hrect | hglue
  · obtain ⟨copy, face, slot, he, _⟩ := hsmall
    cases he
  · obtain ⟨r, ⟨axis, side⟩, he, hz⟩ := hrect
    fin_cases axis
    · simp [doubleCylinderRectangleBoundaryEdge] at he
    · rcases r with ⟨raw, hboundary⟩
      rcases raw with ⟨candidateEdge, k⟩ | interior
      · fin_cases side
        · have hv := congrArg Subtype.val (Sum.inr.inj he)
          rw [subdivisionBoundaryEdgeStart_value] at hv
          change Sum.inr (Sum.inl (oldEdge, index)) =
            subdivisionSegmentStart P x S candidateEdge k at hv
          by_cases hk : k.1 = 0
          · simp [subdivisionSegmentStart, hk] at hv
          · rw [subdivisionSegmentStart, dif_neg hk] at hv
            have hp := Sum.inl.inj (Sum.inr.inj hv)
            have heq : oldEdge = candidateEdge := congrArg Prod.fst hp
            have hik : index.1 = k.1 - 1 := congrArg (fun p => p.2.1) hp
            have hk' : k = next := by apply Fin.ext; dsimp [next]; omega
            right
            apply hz.trans
            apply congrArg zOf
            apply Subtype.ext
            change Sum.inl (candidateEdge, k) = Sum.inl (oldEdge, next)
            rw [← heq, hk']
        · have hv := congrArg Subtype.val (Sum.inr.inj he)
          rw [subdivisionBoundaryEdgeEnd_value] at hv
          change Sum.inr (Sum.inl (oldEdge, index)) =
            subdivisionSegmentEnd P x S candidateEdge k at hv
          by_cases hk : k.1 + 1 = S.half
          · simp [subdivisionSegmentEnd, hk] at hv
          · rw [subdivisionSegmentEnd, dif_neg hk] at hv
            have hp := Sum.inl.inj (Sum.inr.inj hv)
            have heq : oldEdge = candidateEdge := congrArg Prod.fst hp
            have hik : index.1 = k.1 := congrArg (fun p => p.2.1) hp
            have hk' : k = previous := by apply Fin.ext; exact hik.symm
            left
            apply hz.trans
            apply congrArg zOf
            apply Subtype.ext
            change Sum.inl (candidateEdge, k) = Sum.inl (oldEdge, previous)
            rw [← heq, hk']
      · simp [subdivisionBoundaryEdgeMember] at hboundary
  · obtain ⟨q, hxq, qEdge, he, _⟩ := hglue
    rcases qEdge with endEdge | endpoint
    · cases he
    · have hv := congrArg Subtype.val (Sum.inr.inj he)
      cases hv
private theorem rx_horizontal_radial_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half + 1))
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (k : Fin S.half)
    (h : subdivisionHorizontalEdge P x S f i j =
      Sum.inl (⟨Sum.inl radial, member⟩, k)) :
    j.1 = 0 ∧ i = k ∧ xStarFaceXQEdge P x f 0 = ⟨Sum.inl radial, member⟩ := by
  unfold subdivisionHorizontalEdge at h
  split at h
  · rename_i hj
    have hp := Sum.inl.inj h
    exact ⟨hj, congrArg Prod.snd hp, congrArg Prod.fst hp⟩
  · split at h
    · have he := congrArg Subtype.val (congrArg Prod.fst (Sum.inl.inj h))
      cases he
    · cases h
private theorem rx_vertical_radial_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : XStarFace P x) (i : Fin (S.half + 1)) (j : Fin S.half)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (k : Fin S.half)
    (h : subdivisionVerticalEdge P x S f i j =
      Sum.inl (⟨Sum.inl radial, member⟩, k)) :
    i.1 = 0 ∧ j = k ∧ xStarFaceXQEdge P x f 1 = ⟨Sum.inl radial, member⟩ := by
  unfold subdivisionVerticalEdge at h
  split at h
  · rename_i hi
    have hp := Sum.inl.inj h
    exact ⟨hi, congrArg Prod.snd hp, congrArg Prod.fst hp⟩
  · split at h
    · have he := congrArg Subtype.val (congrArg Prod.fst (Sum.inl.inj h))
      cases he
    · cases h
private theorem rx_radial_cell_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (k : Fin S.half) (small : SubdivisionFace P x S) (slot : Two × Two)
    (h : subdivisionFaceBoundaryEdge P x S small slot =
      Sum.inl (⟨Sum.inl radial, member⟩, k)) :
    ∃ corner : Two,
      xStarFaceXQEdge P x small.1 corner = ⟨Sum.inl radial, member⟩ ∧
      small = rxRadialCellAt P S x small.1 corner k := by
  rcases small with ⟨f, i, j⟩
  rcases slot with ⟨axis, side⟩
  fin_cases axis <;> fin_cases side
  · change subdivisionHorizontalEdge P x S f i
        (⟨j.1, by have := j.2; omega⟩ : Fin (S.half + 1)) =
        Sum.inl (⟨Sum.inl radial, member⟩, k) at h
    obtain ⟨hj, hi, he⟩ := rx_horizontal_radial_coordinates P S x f i _ radial member k h
    have hj' : j = (⟨0, S.half_pos⟩ : Fin S.half) := Fin.ext hj
    exact ⟨0, he, by simp [rxRadialCellAt, hi, hj']⟩
  · change subdivisionHorizontalEdge P x S f i
        (⟨j.1 + 1, by have := j.2; omega⟩ : Fin (S.half + 1)) =
        Sum.inl (⟨Sum.inl radial, member⟩, k) at h
    obtain ⟨hj, _, _⟩ := rx_horizontal_radial_coordinates P S x f i _ radial member k h
    change j.1 + 1 = 0 at hj
    omega
  · change subdivisionVerticalEdge P x S f
        (⟨i.1, by have := i.2; omega⟩ : Fin (S.half + 1)) j =
        Sum.inl (⟨Sum.inl radial, member⟩, k) at h
    obtain ⟨hi, hj, he⟩ := rx_vertical_radial_coordinates P S x f _ j radial member k h
    have hi' : i = (⟨0, S.half_pos⟩ : Fin S.half) := Fin.ext hi
    exact ⟨1, he, by simp [rxRadialCellAt, hi', hj]⟩
  · change subdivisionVerticalEdge P x S f
        (⟨i.1 + 1, by have := i.2; omega⟩ : Fin (S.half + 1)) j =
        Sum.inl (⟨Sum.inl radial, member⟩, k) at h
    obtain ⟨hi, _, _⟩ := rx_vertical_radial_coordinates P S x f _ j radial member k h
    change i.1 + 1 = 0 at hi
    omega
private theorem qZDegree_rx_radial_le
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X) (copy : Two)
    (radial : XQEdge P) (member : xStarEdgeMember P x (Sum.inl radial) = true)
    (k : Fin S.half) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inl radial, member⟩, k))⟩) ≤
        qZDegree P radial.1.2 := by
  classical
  let neighbour : RXRadialFaceCorner P x radial member → RX2 P S := fun fc =>
    Sum.inl (Sum.inl ⟨x, Sum.inl
      (copy, rxRadialCellAt P S x fc.1.1 fc.1.2 k)⟩)
  have cover : ∀ z, rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inl radial, member⟩, k))⟩) z = true →
      ∃ fc, neighbour fc = z := by
    intro z hz
    rcases rx_local_z_cases P S x _ z hz with hsmall | hrect | hglue
    · obtain ⟨c, small, slot, he, hz⟩ := hsmall
      have hp := Sum.inl.inj he
      have hc : copy = c := congrArg Prod.fst hp
      have he' := (congrArg Prod.snd hp).symm
      obtain ⟨corner, hedge, hcell⟩ := rx_radial_cell_cases P S x radial member k small slot he'
      refine ⟨⟨(small.1, corner), hedge⟩, ?_⟩
      rw [hz]
      simp only [neighbour]
      rw [← hc]
      exact congrArg (fun sf : SubdivisionFace P x S =>
        (Sum.inl (Sum.inl ⟨x, Sum.inl (copy, sf)⟩) : RX2 P S)) hcell.symm
    · obtain ⟨rectangle, ⟨axis, side⟩, he, _⟩ := hrect
      fin_cases axis
      · have hp := Sum.inl.inj he
        have hr := congrArg Prod.snd hp
        change Sum.inl (⟨Sum.inl radial, member⟩, k) = rectangle.1 at hr
        have hm := rectangle.2
        rw [← hr] at hm
        simp [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember] at hm
      · fin_cases side <;> cases he
    · obtain ⟨q, hxq, qEdge, he, _⟩ := hglue
      rcases qEdge with ⟨c, e, segment⟩ | endpoint
      · have hp := Sum.inl.inj he
        have hr := congrArg Prod.snd hp
        have old := congrArg Subtype.val (congrArg Prod.fst (Sum.inl.inj hr))
        cases old
      · cases he
  exact (card_fiber_le_of_covered
    (fun z : RX2 P S => rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inl radial, member⟩, k))⟩) z = true)
    neighbour cover).trans
    (radialFaceCorner_card_le P x radial member)
private theorem rx_horizontal_boundary_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half + 1))
    (boundary : QZEdge P) (member : xStarEdgeMember P x (Sum.inr boundary) = true)
    (k : Fin S.half)
    (h : subdivisionHorizontalEdge P x S f i j =
      Sum.inl (⟨Sum.inr boundary, member⟩, k)) :
    j.1 = S.half ∧ i = k ∧ xStarFaceQZEdge P x f 1 = ⟨Sum.inr boundary, member⟩ := by
  unfold subdivisionHorizontalEdge at h
  split at h
  · have he := congrArg Subtype.val (congrArg Prod.fst (Sum.inl.inj h))
    cases he
  · split at h
    · rename_i hj
      have hp := Sum.inl.inj h
      exact ⟨hj, congrArg Prod.snd hp, congrArg Prod.fst hp⟩
    · cases h
private theorem rx_vertical_boundary_coordinates
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : XStarFace P x) (i : Fin (S.half + 1)) (j : Fin S.half)
    (boundary : QZEdge P) (member : xStarEdgeMember P x (Sum.inr boundary) = true)
    (k : Fin S.half)
    (h : subdivisionVerticalEdge P x S f i j =
      Sum.inl (⟨Sum.inr boundary, member⟩, k)) :
    i.1 = S.half ∧ j = k ∧ xStarFaceQZEdge P x f 0 = ⟨Sum.inr boundary, member⟩ := by
  unfold subdivisionVerticalEdge at h
  split at h
  · have he := congrArg Subtype.val (congrArg Prod.fst (Sum.inl.inj h))
    cases he
  · split at h
    · rename_i hi
      have hp := Sum.inl.inj h
      exact ⟨hi, congrArg Prod.snd hp, congrArg Prod.fst hp⟩
    · cases h
private theorem rx_boundary_cell_cases
    (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (boundary : QZEdge P) (member : xStarEdgeMember P x (Sum.inr boundary) = true)
    (k : Fin S.half) (small : SubdivisionFace P x S) (slot : Two × Two)
    (h : subdivisionFaceBoundaryEdge P x S small slot =
      Sum.inl (⟨Sum.inr boundary, member⟩, k)) :
    ∃ corner : Two,
      xStarFaceQZEdge P x small.1 corner = ⟨Sum.inr boundary, member⟩ ∧
      small = rxBoundaryCellAt P S x small.1 corner k := by
  rcases small with ⟨f, i, j⟩
  rcases slot with ⟨axis, side⟩
  fin_cases axis <;> fin_cases side
  · change subdivisionHorizontalEdge P x S f i
        (⟨j.1, by have := j.2; omega⟩ : Fin (S.half + 1)) =
        Sum.inl (⟨Sum.inr boundary, member⟩, k) at h
    obtain ⟨hj, _, _⟩ := rx_horizontal_boundary_coordinates P S x f i _ boundary member k h
    change j.1 = S.half at hj
    have := j.2
    omega
  · change subdivisionHorizontalEdge P x S f i
        (⟨j.1 + 1, by have := j.2; omega⟩ : Fin (S.half + 1)) =
        Sum.inl (⟨Sum.inr boundary, member⟩, k) at h
    obtain ⟨hj, hi, he⟩ := rx_horizontal_boundary_coordinates P S x f i _ boundary member k h
    change j.1 + 1 = S.half at hj
    have hj' : j = rxStarEdgeInteriorLastIndex S := by
      apply Fin.ext
      change j.1 = S.half - 1
      omega
    exact ⟨1, he, by simp [rxBoundaryCellAt, hi, hj']⟩
  · change subdivisionVerticalEdge P x S f
        (⟨i.1, by have := i.2; omega⟩ : Fin (S.half + 1)) j =
        Sum.inl (⟨Sum.inr boundary, member⟩, k) at h
    obtain ⟨hi, _, _⟩ := rx_vertical_boundary_coordinates P S x f _ j boundary member k h
    change i.1 = S.half at hi
    have := i.2
    omega
  · change subdivisionVerticalEdge P x S f
        (⟨i.1 + 1, by have := i.2; omega⟩ : Fin (S.half + 1)) j =
        Sum.inl (⟨Sum.inr boundary, member⟩, k) at h
    obtain ⟨hi, hj, he⟩ := rx_vertical_boundary_coordinates P S x f _ j boundary member k h
    change i.1 + 1 = S.half at hi
    have hi' : i = rxStarEdgeInteriorLastIndex S := by
      apply Fin.ext
      change i.1 = S.half - 1
      omega
    exact ⟨0, he, by simp [rxBoundaryCellAt, hi', hj]⟩
private theorem qZDegree_rx_boundary_le_three
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (S : OddScale) (x : P.X) (copy : Two)
    (boundary : QZEdge P) (member : xStarEdgeMember P x (Sum.inr boundary) = true)
    (k : Fin S.half) :
    qZDegree (rxReplacementPresentation P S)
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inr boundary, member⟩, k))⟩) ≤ 3 := by
  classical
  let rectangle : SubdivisionBoundaryEdge P x S :=
    ⟨Sum.inl (⟨Sum.inr boundary, member⟩, k), by
      simpa [subdivisionBoundaryEdgeMember, xStarBoundaryEdgeMember, xStarEdgeMember]
        using member⟩
  let qEdge : QDoubleCylinderEdge P boundary.1.1 S :=
    Sum.inl (copy, (⟨boundary.1.2, boundary.2⟩ : QStarEdge P boundary.1.1), k)
  let neighbour : (RXBoundaryFaceCorner P x boundary member ⊕ Two) → RX2 P S
    | Sum.inl fc => Sum.inl (Sum.inl ⟨x, Sum.inl
        (copy, rxBoundaryCellAt P S x fc.1.1 fc.1.2 k)⟩)
    | Sum.inr bit => if bit = 0 then Sum.inl (Sum.inl ⟨x, Sum.inr rectangle⟩)
        else Sum.inl (Sum.inr ⟨boundary.1.1, qEdge⟩)
  have cover : ∀ z, rxQZIncidence P S
      (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inr boundary, member⟩, k))⟩) z = true →
      ∃ tag, neighbour tag = z := by
    intro z hz
    rcases rx_local_z_cases P S x _ z hz with hsmall | hrect | hglue
    · obtain ⟨c, small, slot, he, hz⟩ := hsmall
      have hp := Sum.inl.inj he
      have hc : copy = c := congrArg Prod.fst hp
      have he' := (congrArg Prod.snd hp).symm
      obtain ⟨corner, hedge, hcell⟩ :=
        rx_boundary_cell_cases P S x boundary member k small slot he'
      refine ⟨Sum.inl ⟨(small.1, corner), hedge⟩, ?_⟩
      rw [hz]
      simp only [neighbour]
      rw [← hc]
      exact congrArg (fun sf : SubdivisionFace P x S =>
        (Sum.inl (Sum.inl ⟨x, Sum.inl (copy, sf)⟩) : RX2 P S)) hcell.symm
    · obtain ⟨r, ⟨axis, side⟩, he, hz⟩ := hrect
      fin_cases axis
      · have hp := Sum.inl.inj he
        have hr : rectangle = r := Subtype.ext (congrArg Prod.snd hp)
        refine ⟨Sum.inr 0, ?_⟩
        simpa only [neighbour, if_pos rfl, hr] using hz.symm
      · fin_cases side <;> cases he
    · obtain ⟨q, hxq, qe, he, hz⟩ := hglue
      rcases qe with ⟨c, e, segment⟩ | endpoint
      · have hp := Sum.inl.inj he
        have hc : copy = c := congrArg Prod.fst hp
        have hs := Sum.inl.inj (congrArg Prod.snd hp)
        have hk : k = segment := congrArg Prod.snd hs
        have hold := Sum.inr.inj (congrArg Subtype.val (congrArg Prod.fst hs))
        have hq : boundary.1.1 = q := congrArg (fun e : QZEdge P => e.1.1) hold
        have hez : boundary.1.2 = e.1 := congrArg (fun e : QZEdge P => e.1.2) hold
        subst q
        have he' : e = (⟨boundary.1.2, boundary.2⟩ : QStarEdge P boundary.1.1) :=
          Subtype.ext hez.symm
        refine ⟨Sum.inr 1, ?_⟩
        rw [hz]
        simp [neighbour, qEdge, ← hc, ← hk, he']
      · cases he
  calc
    _ ≤ Fintype.card (RXBoundaryFaceCorner P x boundary member ⊕ Two) :=
      card_fiber_le_of_covered
        (fun z : RX2 P S => rxQZIncidence P S
          (Sum.inl ⟨x, Sum.inl (copy, Sum.inl (⟨Sum.inr boundary, member⟩, k))⟩) z = true)
        neighbour cover
    _ = Fintype.card (RXBoundaryFaceCorner P x boundary member) + 2 := by simp
    _ ≤ 3 := by have := boundaryFaceCorner_card_le_one P R x boundary member; omega
private theorem qZDegree_rx_local_le_four
    (P : TannerSquarePresentation) (_A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (hB : BoundedValence P)
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    qZDegree (rxReplacementPresentation P S) (Sum.inl ⟨x, edge⟩) ≤ 4 := by
  rcases edge with ⟨copy, edge⟩ | ⟨vertex, member⟩
  · rcases edge with ⟨⟨rawEdge, edgeMember⟩, segment⟩ | interior
    · rcases rawEdge with radial | boundary
      · exact (qZDegree_rx_radial_le P S x copy radial edgeMember segment).trans
          (hB.2.2 radial.1.2).2.1
      · exact (qZDegree_rx_boundary_le_three P R S x copy boundary edgeMember segment).trans
          (by decide)
    · rcases interior with ⟨face, i, j⟩ | ⟨face, i, j⟩
      · exact qZDegree_rx_horizontal_le_four P S x copy face i j
      · exact qZDegree_rx_vertical_grid_le_four P S x copy face i j
  · rcases vertex with ⟨vertex, starMember⟩ | interior
    · rcases vertex with oldX | oldQ | oldZ
      · simp [subdivisionBoundaryVertexMember, xStarBoundaryVertexMember] at member
      · exact (qZDegree_rx_vertical_oldQ_le P S x oldQ member).trans
          (hB.2.2 oldQ).2.1
      · exact qZDegree_rx_vertical_oldZ_le_four P R S x oldZ member
    · rcases interior with ⟨oldEdge, index⟩ | faceInterior
      · exact (qZDegree_rx_vertical_boundaryInterior_le_two P S x oldEdge index member).trans
          (by decide)
      · simp [subdivisionBoundaryVertexMember] at member
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
open BDL26BoundedValence
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (rxReplacementPresentation P S) := by
  refine ⟨BDL26RXLocalReplacement.rx_x_bounded P A4 R S h,
    BDL26RXLocalReplacement.rx_z_bounded P S h, ?_⟩
  intro q
  rcases q with ⟨x, edge⟩ | ⟨oldQ, vertex⟩
  · have hx := qXDegree_rx_local_le_two P S x edge
    have hz := qZDegree_rx_local_le_four P A4 R S h x edge
    exact ⟨hx.trans (by decide), hz, by omega⟩
  · exact rx_shifted_bounded P A4.toTannerSquareAdmissible S h oldQ vertex
end QEC.Coding.BDL26RXLocalReplacement
