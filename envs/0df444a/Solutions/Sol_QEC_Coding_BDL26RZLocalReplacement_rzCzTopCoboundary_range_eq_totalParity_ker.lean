-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzCzTopCoboundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:03:33.711591+00:00
-- url     : https://prove2.me/submissions/a89ef5df-e9b9-4f94-b799-f115105cb8f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
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
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_pathChain
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_totalParity_graphBoundary
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
namespace BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
private theorem graphBoundary_range_eq_totalParity_ker_of_nonempty_paths
    {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex,
      Nonempty (UndirectedPath edgeStart edgeEnd root vertex)) :
    LinearMap.range (graphBoundary edgeStart edgeEnd) =
      LinearMap.ker totalParity := by
  classical
  ext word
  constructor
  · rintro ⟨chain, rfl⟩
    rw [LinearMap.mem_ker]
    exact totalParity_graphBoundary edgeStart edgeEnd chain
  · intro hword
    rw [LinearMap.mem_ker] at hword
    have hfinite : ∀ vertices : Finset Vertex,
        ∃ chain : Word Field Edge,
          graphBoundary edgeStart edgeEnd chain =
            ∑ vertex ∈ vertices,
              word vertex •
                (Pi.single root 1 + Pi.single vertex 1) := by
      intro vertices
      induction vertices using Finset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | @insert vertex vertices hnot ih =>
          obtain ⟨previous, hprevious⟩ := ih
          obtain ⟨path⟩ := paths vertex
          refine ⟨previous + word vertex • pathChain path, ?_⟩
          rw [map_add, map_smul, hprevious,
            graphBoundary_pathChain edgeStart edgeEnd root]
          simp only [smul_add]
          rw [Finset.sum_insert hnot]
          abel
    obtain ⟨chain, hchain⟩ := hfinite Finset.univ
    refine ⟨chain, ?_⟩
    rw [hchain]
    simp only [smul_add, Finset.sum_add_distrib]
    have hroot :
        (∑ vertex : Vertex, word vertex • Pi.single root 1) =
          Pi.single root (totalParity word) := by
      ext vertex
      by_cases hvertex : vertex = root
      · subst vertex
        simp [totalParity]
      · simp [hvertex]
    have hdecomposition :
        (∑ vertex : Vertex, word vertex • Pi.single vertex 1) = word := by
      calc
        (∑ vertex : Vertex, word vertex • Pi.single vertex 1) =
            ∑ vertex : Vertex, Pi.single vertex (word vertex) := by
          apply Finset.sum_congr rfl
          intro vertex _
          ext target
          by_cases htarget : target = vertex
          · subst target
            simp
          · simp [htarget]
        _ = word := word_eq_sum_single (F := Field) word
    rw [hroot, hdecomposition, hword]
    simp
private theorem subdivisionHorizontalPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face (rzGridIndex S step hstep) 0)) := by
  induction step with
  | zero =>
      exact ⟨by simpa [rzGridIndex] using
        (UndirectedPath.nil : UndirectedPath
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          (subdivisionGridVertex P x S face 0 0)
          (subdivisionGridVertex P x S face 0 0))⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      let edge := subdivisionHorizontalEdge P x S face index (0 : Fin (S.half + 1))
      refine ⟨UndirectedPath.step (by
          simpa [rzGridIndex, index] using path) edge ?_⟩
      apply Or.inl
      constructor
      · exact subdivisionHorizontalEdge_start P x S face index
            (0 : Fin (S.half + 1))
      · exact subdivisionHorizontalEdge_end P x S face index
            (0 : Fin (S.half + 1))
private theorem subdivisionVerticalPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i : Fin (S.half + 1))
    (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face i 0)
      (subdivisionGridVertex P x S face i (rzGridIndex S step hstep))) := by
  induction step with
  | zero =>
      exact ⟨by simpa [rzGridIndex] using
        (UndirectedPath.nil : UndirectedPath
          (subdivisionEdgeStart P x S) (subdivisionEdgeEnd P x S)
          (subdivisionGridVertex P x S face i 0)
          (subdivisionGridVertex P x S face i 0))⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      let edge := subdivisionVerticalEdge P x S face i index
      refine ⟨UndirectedPath.step (by
          simpa [rzGridIndex, index] using path) edge ?_⟩
      apply Or.inl
      constructor
      · exact subdivisionVerticalEdge_start P x S face i index
      · exact subdivisionVerticalEdge_end P x S face i index
private theorem subdivisionGridPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (i j : Fin (S.half + 1)) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face i j)) := by
  have hi : i.1 ≤ S.half := by omega
  have hj : j.1 ≤ S.half := by omega
  obtain ⟨horizontal⟩ :=
    subdivisionHorizontalPrefixPath_nonempty P x S face i.1 hi
  obtain ⟨vertical⟩ :=
    subdivisionVerticalPrefixPath_nonempty P x S face i j.1 hj
  have horizontal' : UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face 0 0)
      (subdivisionGridVertex P x S face i 0) := by
    simpa [rzGridIndex] using horizontal
  have vertical' : UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S)
      (subdivisionGridVertex P x S face i 0)
      (subdivisionGridVertex P x S face i j) := by
    simpa [rzGridIndex] using vertical
  exact ⟨horizontal'.append vertical'⟩
private theorem subdivisionOriginalVertexPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (vertex : XStarVertex P x) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (rzSubdivisionCenter P x S)
      (Sum.inl vertex)) := by
  rcases vertex with ⟨value, hvalue⟩
  rcases value with oldX | q | z
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    subst oldX
    have hxface : P.faceX face0.1 = x := by
      simpa [xStarFaceMember] using face0.2
    obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face0 0 0
    exact ⟨by simpa [rzSubdivisionCenter, subdivisionGridVertex,
      xStarFaceXVertex, hxface] using path⟩
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨faceValue, hface, hq | hq⟩ := hvalue
    · subst q
      let face : XStarFace P x := ⟨faceValue, hface⟩
      have hxface : P.faceX faceValue = x := by
        simpa [xStarFaceMember] using hface
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        (rzGridLast S) 0
      exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
        subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
        face, hxface, S.half_pos.ne']
        using path⟩
    · subst q
      let face : XStarFace P x := ⟨faceValue, hface⟩
      have hxface : P.faceX faceValue = x := by
        simpa [xStarFaceMember] using hface
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        0 (rzGridLast S)
      exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
        subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
        face, hxface, S.half_pos.ne']
        using path⟩
  · simp only [xStarVertexMember, decide_eq_true_eq] at hvalue
    obtain ⟨faceValue, hface, hz⟩ := hvalue
    subst z
    let face : XStarFace P x := ⟨faceValue, hface⟩
    have hxface : P.faceX faceValue = x := by
      simpa [xStarFaceMember] using hface
    obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
      (rzGridLast S) (rzGridLast S)
    exact ⟨by simpa [rzSubdivisionCenter, rzGridLast,
      subdivisionGridVertex, xStarFaceXVertex, xStarFaceQVertex,
      xStarFaceZVertex, face, hxface, S.half_pos.ne']
      using path⟩
private theorem subdivisionSegmentPrefixPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarEdge P x) (step : Nat) (hstep : step ≤ S.half) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (Sum.inl (xStarEdgeStart P x edge))
      (rzSubdivisionSegmentVertex P x S edge step hstep)) := by
  induction step with
  | zero => exact ⟨UndirectedPath.nil⟩
  | succ previous ih =>
      have hprevious : previous ≤ S.half := by omega
      have hindex : previous < S.half := by omega
      obtain ⟨path⟩ := ih hprevious
      let index : Fin S.half := ⟨previous, hindex⟩
      refine ⟨UndirectedPath.step (by
          simpa [rzSubdivisionSegmentVertex, index] using path)
        (Sum.inl (edge, index)) ?_⟩
      apply Or.inl
      constructor
      · have hnotlast : previous ≠ S.half := by omega
        simp [subdivisionEdgeStart, subdivisionSegmentStart,
          index, hnotlast]
      · simp [subdivisionEdgeEnd, subdivisionSegmentEnd,
          rzSubdivisionSegmentVertex, index]
private theorem subdivisionVertexPath_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (vertex : SubdivisionVertex P x S) :
    Nonempty (UndirectedPath (subdivisionEdgeStart P x S)
      (subdivisionEdgeEnd P x S) (rzSubdivisionCenter P x S) vertex) := by
  rcases vertex with original | remaining
  · exact subdivisionOriginalVertexPath_nonempty P x S face0 original
  · rcases remaining with edgeInterior | faceInterior
    · rcases edgeInterior with ⟨edge, index⟩
      obtain ⟨toStart⟩ := subdivisionOriginalVertexPath_nonempty
        P x S face0 (xStarEdgeStart P x edge)
      have hstep : index.1 + 1 ≤ S.half := by
        have := index.2
        have := S.half_pos
        omega
      obtain ⟨alongEdge⟩ := subdivisionSegmentPrefixPath_nonempty
        P x S edge (index.1 + 1) hstep
      have hzero : index.1 + 1 ≠ 0 := by omega
      have hlast : index.1 + 1 ≠ S.half := by
        have := index.2
        omega
      exact ⟨toStart.append (by simpa [rzSubdivisionSegmentVertex,
        hzero, hlast] using alongEdge)⟩
    · rcases faceInterior with ⟨face, i, j⟩
      have hxface : P.faceX face.1 = x := by
        simpa [xStarFaceMember] using face.2
      have hi0 : i.1 + 1 ≠ 0 := by omega
      have hj0 : j.1 + 1 ≠ 0 := by omega
      have hilast : i.1 + 1 ≠ S.half := by
        have := i.2
        omega
      have hjlast : j.1 + 1 ≠ S.half := by
        have := j.2
        omega
      obtain ⟨path⟩ := subdivisionGridPath_nonempty P x S face
        ⟨i.1 + 1, by have := i.2; have := S.half_pos; omega⟩
        ⟨j.1 + 1, by have := j.2; have := S.half_pos; omega⟩
      simp only [rzSubdivisionCenter, subdivisionGridVertex,
        xStarFaceXVertex, hxface, hi0, hj0, hilast, hjlast,
        if_false, if_true] at path ⊢
      exact ⟨path⟩
private theorem admissibleXBoundary_has_face
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    Nonempty (XStarFace P x) := by
  rcases A.xBoundaryRoot x with ⟨value, hboundary⟩
  rcases value with oldX | q | z
  · simp [xStarBoundaryVertexMember] at hboundary
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hboundary
    obtain ⟨face, hface, _⟩ := hboundary
    exact ⟨⟨face, hface⟩⟩
  · simp only [xStarBoundaryVertexMember, decide_eq_true_eq] at hboundary
    obtain ⟨face, hface, _⟩ := hboundary
    exact ⟨⟨face, hface⟩⟩
private theorem subdivisionPathAtCopy_nonempty
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face0 : XStarFace P x) (copy : Two)
    (vertex : SubdivisionVertex P x S) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (copy, rzSubdivisionCenter P x S) (copy, vertex)) := by
  obtain ⟨path⟩ := subdivisionVertexPath_nonempty P x S face0 vertex
  exact ⟨UndirectedPath.map
    (edgeStart := subdivisionEdgeStart P x S)
    (edgeEnd := subdivisionEdgeEnd P x S)
    (edgeStart' := tannerDoubleCylinderEdgeStart P x S)
    (edgeEnd' := tannerDoubleCylinderEdgeEnd P x S)
    (fun subdivisionVertex => (copy, subdivisionVertex))
    (fun subdivisionEdge => Sum.inl (copy, subdivisionEdge))
    (fun _ => rfl) (fun _ => rfl) path⟩
private theorem doubleCylinderPath_nonempty
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (vertex : DoubleCylinderVertex P x S) :
    Nonempty (UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
      (tannerDoubleCylinderEdgeEnd P x S)
      (0, rzSubdivisionCenter P x S) vertex) := by
  obtain ⟨face0⟩ := admissibleXBoundary_has_face P A x
  rcases vertex with ⟨copy, vertex⟩
  fin_cases copy
  · exact subdivisionPathAtCopy_nonempty P x S face0 0 vertex
  · let boundaryVertex : SubdivisionBoundaryVertex P x S :=
      subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)
    obtain ⟨toBoundaryZero⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 0 boundaryVertex.1
    obtain ⟨toBoundaryOne⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 1 boundaryVertex.1
    obtain ⟨toVertexOne⟩ := subdivisionPathAtCopy_nonempty
      P x S face0 1 vertex
    let bridge : UndirectedPath (tannerDoubleCylinderEdgeStart P x S)
        (tannerDoubleCylinderEdgeEnd P x S)
        (0, boundaryVertex.1) (1, boundaryVertex.1) :=
      .step .nil (Sum.inr boundaryVertex) (Or.inl ⟨rfl, rfl⟩)
    exact ⟨toBoundaryZero.append
      (bridge.append (toBoundaryOne.reverse.append toVertexOne))⟩
attribute [instance] baseScaleFiveRzXFintype baseScaleFiveRzQFintype
  baseScaleFiveRzZFintype baseScaleFiveRzFaceFintype
end BDL26RZLocalReplacement
end Coding
end QEC
end

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (z : P.Z) (S : OddScale) :
    LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2) =
      LinearMap.ker totalParity := by
  classical
  rw [rzCzTopCoboundary_eq_graphBoundary]
  exact graphBoundary_range_eq_totalParity_ker_of_nonempty_paths
    (tannerDoubleCylinderEdgeStart (transposePresentation P) z S)
    (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S)
    (0, rzSubdivisionCenter (transposePresentation P) z S)
    (doubleCylinderPath_nonempty (transposePresentation P)
      (transposeTannerSquareAdmissible P A) z S)
end QEC.Coding.BDL26RZLocalReplacement
