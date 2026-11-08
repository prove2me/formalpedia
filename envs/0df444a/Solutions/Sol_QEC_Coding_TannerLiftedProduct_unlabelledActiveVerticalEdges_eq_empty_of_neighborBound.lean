-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:17:34.4924+00:00
-- url     : https://prove2.me/submissions/0194f3a2-8b8a-4d36-8560-3002e6493811

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceRow_weight_le_activeVerticalEdge_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_unlabelledActiveVerticalEdges_subset_activeVerticalEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActive_of_mem_unlabelledActiveVerticalEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdgeAt_verticalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceActiveVerticalEdge_faceWeight_ge
import Theorems.Thm_QEC_Coding_SmallSetExpansion_subset_eq_empty_of_internal_expansion_and_external_degree_lt


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hNeighborBound : ∀ e ∈ unlabelledActiveVerticalEdges label c L,
      (∑ e' ∈ activeVerticalEdges label c \
          unlabelledActiveVerticalEdges label c L,
          verticalFaceGraph label e e') ≤
        (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
        ∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by
  apply SmallSetExpansion.subset_eq_empty_of_internal_expansion_and_external_degree_lt
    (verticalFaceGraph label) radius lambda
    (activeVerticalEdges label c)
    (unlabelledActiveVerticalEdges label c L) d m hExpand
    (unlabelledActiveVerticalEdges_subset_activeVerticalEdges label c L)
    hActiveRadius
  · intro e he
    have hFaceActive := isFaceActive_of_mem_unlabelledActiveVerticalEdges
      label c L hClosed.1 e he
    exact (faceActiveVerticalEdge_faceWeight_ge
      label h g' c hcCycle d hDistance e hFaceActive).trans
        (localFaceRow_weight_le_activeVerticalEdge_degree label c e)
  · intro e he
    have heData := Finset.mem_filter.mp he
    have hFaceActive := isFaceActive_of_mem_unlabelledActiveVerticalEdges
      label c L hClosed.1 e he
    have hSourceIncident : IsIncidentToFaceActiveVerticalEdge label c
        (verticalEdgeEndpoint label e 0) :=
      ⟨e.2.1, hFaceActive⟩
    have hTargetIncident : IsIncidentToFaceActiveVerticalEdge label c
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) :=
      ⟨e.2.1,
        isFaceActiveVerticalEdgeAt_verticalNeighbor label c
          (verticalEdgeEndpoint label e 0) e.2.1 hFaceActive⟩
    have hSourceDegree :
        (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) < m := by
      apply Nat.lt_of_not_ge
      intro hDegree
      exact heData.2.1
        (hClosed.2 (verticalEdgeEndpoint label e 0)
          hSourceIncident hDegree)
    have hTargetDegree :
        (∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u) <
            m := by
      apply Nat.lt_of_not_ge
      intro hDegree
      exact heData.2.2
        (hClosed.2
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
          hTargetIncident hDegree)
    exact (hNeighborBound e he).trans_lt (by omega)
  · exact hThreshold
end QEC.Coding.TannerLiftedProduct
