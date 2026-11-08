-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_globalExpansion_of_labelledVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:00.775423+00:00
-- url     : https://prove2.me/submissions/177244a0-192f-42eb-908f-f376d1924cc9

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_isClosed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_nonactive_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled

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
    (d m s : Nat) (beta : ℝ)
    (hEdgeLabel : ∀ v b, IsFaceActiveVerticalEdgeAt label c v b →
      v ∈ labelledVertices label c m ∨
        verticalNeighbor label v b ∈ labelledVertices label c m)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : (labelledVertices label c m).card ≤ radiusEdge)
    (hLRadiusFace : (labelledVertices label c m).card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  have hClosed := labelledVertices_isClosed label c m
  have hCarriesLabel : ∀ v b,
      CarriesActiveFaceVerticalEdgeAt label c v b →
        v ∈ labelledVertices label c m ∨
          verticalNeighbor label v b ∈ labelledVertices label c m := by
    intro v b hCarries
    by_cases hv : v ∈ vertexBlockSupport c
    · exact Or.inl (hClosed.1 hv)
    by_cases hNeighbor : verticalNeighbor label v b ∈ vertexBlockSupport c
    · exact Or.inr (hClosed.1 hNeighbor)
    · exact hEdgeLabel v b ⟨hCarries, hv, hNeighbor⟩
  apply cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
    label h hRank g' gInjective c hcCycle hcLocal
    (labelledVertices label c m)
    hClosed.1 hCarriesLabel
    d m s beta
    (fun v hv hvInactive =>
      labelledVertices_nonactive_degree label c m v hv hvInactive)
    hExpand hDistance hLength hDistanceScale hRectangleScale hBudget
    radiusEdge radiusFace lambdaEdge lambdaFace hLambdaEdge hLambdaFace
    hExpandEdge hExpandFace hLRadiusEdge hLRadiusFace
    hThresholdEdge hThresholdFace
end QEC.Coding.TannerLiftedProduct
