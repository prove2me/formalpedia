-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_globalExpansion_of_blockWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:29:29.384245+00:00
-- url     : https://prove2.me/submissions/6bf71c7f-14a4-4ab4-83fa-a22a25693ee0

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeVerticalEdges_le_card_mul_blockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_labelledVertices_le_blockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_globalExpansion_of_expandingVerticalEdges

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
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusVertical : Nat) (lambdaVertical : ℝ)
    (hExpandVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radiusVertical lambdaVertical)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight c ≤ radiusVertical)
    (hVerticalThreshold : (2 * m : ℝ) + lambdaVertical ≤ d)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hBlockRadiusEdge : blockWeight c ≤ radiusEdge)
    (hBlockRadiusFace : blockWeight c ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  apply cycle_eq_zero_of_globalExpansion_of_expandingVerticalEdges
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
    hProductExpand hDistance hLength hDistanceScale hRectangleScale hBudget
    radiusVertical lambdaVertical hExpandVertical
  · exact (card_activeVerticalEdges_le_card_mul_blockWeight
      label c hTwo).trans hBlockRadiusVertical
  · exact hVerticalThreshold
  · exact hLambdaEdge
  · exact hLambdaFace
  · exact hExpandEdge
  · exact hExpandFace
  · exact (card_labelledVertices_le_blockWeight
      label h g' c hcCycle d m hDistance hFour).trans hBlockRadiusEdge
  · exact (card_labelledVertices_le_blockWeight
      label h g' c hcCycle d m hDistance hFour).trans hBlockRadiusFace
  · exact hThresholdEdge
  · exact hThresholdFace
end QEC.Coding.TannerLiftedProduct
