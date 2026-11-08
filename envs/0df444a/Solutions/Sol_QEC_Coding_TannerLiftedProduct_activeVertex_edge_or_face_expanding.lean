-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.activeVertex_edge_or_face_expanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:12:05.725957+00:00
-- url     : https://prove2.me/submissions/bb80c201-46f6-4262-8d56-bc712e2f8608

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_adjacencyGraph_eq_card_directionsInto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_horizontalDirectionsInto_add_outside
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_verticalDirectionsInto_add_outside
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_restrictedWeight_le_sum_faceSquareGraph
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalDirectionsOutside_subset_inactive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localStar_restrictedWeight_ge_on
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero


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
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (hOpposite : ∀ v ∈ vertexBlockSupport c,
      ∀ a ∈ horizontalDirectionsOutside label L v,
      ∀ b ∈ verticalDirectionsOutside label L v,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L)
    (v : VertexIndex G) (hv : v ∈ vertexBlockSupport c)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
      s ≤ ∑ u ∈ L, faceSquareGraph label v u := by
  by_cases hEdge : m ≤ ∑ u ∈ L, adjacencyGraph label v u
  · exact Or.inl hEdge
  · right
    have hAdjacency := sum_adjacencyGraph_eq_card_directionsInto
      label L v
    have hHorizontalSmall :
        (horizontalDirectionsInto label L v).card < m := by
      omega
    have hVerticalSmall :
        (verticalDirectionsInto label L v).card < m := by
      omega
    have hHorizontalPartition := card_horizontalDirectionsInto_add_outside
      label L v
    have hVerticalPartition := card_verticalDirectionsInto_add_outside
      label L v
    have hHorizontalLarge : Fintype.card W - m <
        (horizontalDirectionsOutside label L v).card := by
      omega
    have hVerticalLarge : Fintype.card W - m <
        (verticalDirectionsOutside label L v).card := by
      omega
    have hLocal := localStar_restrictedWeight_ge_on
      label h hRank g' gInjective c hcCycle hcLocal v
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero c v).1 hv)
      (horizontalDirectionsOutside label L v)
      (verticalDirectionsOutside label L v)
      (verticalDirectionsOutside_subset_inactive label c L hActive v)
      d m s beta hExpand hDistance hHorizontalLarge hVerticalLarge
      hDistanceScale hRectangleScale hBudget
    exact hLocal.trans (restrictedWeight_le_sum_faceSquareGraph
      label c v
      (horizontalDirectionsOutside label L v)
      (verticalDirectionsOutside label L v) L
      (hOpposite v hv))
end QEC.Coding.TannerLiftedProduct
