-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_globalExpansion_of_expandingVerticalEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:27:14.053129+00:00
-- url     : https://prove2.me/submissions/a6cf97b9-a1ad-456f-8284-dc158e9be60a

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceActiveVerticalEdge_has_labelledEndpoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_globalExpansion_of_labelledVertices
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_isClosed


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
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusVertical : Nat) (lambdaVertical : ℝ)
    (hExpandVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radiusVertical lambdaVertical)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radiusVertical)
    (hVerticalThreshold : (2 * m : ℝ) + lambdaVertical ≤ d)
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
  apply cycle_eq_zero_of_globalExpansion_of_labelledVertices
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
  · intro v b he
    exact faceActiveVerticalEdge_has_labelledEndpoint
      label h g' c hcCycle d m radiusVertical lambdaVertical hDistance
      (labelledVertices label c m) (labelledVertices_isClosed label c m)
      hExpandVertical hActiveRadius hVerticalThreshold v b he
  · exact hProductExpand
  · exact hDistance
  · exact hLength
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambdaEdge
  · exact hLambdaFace
  · exact hExpandEdge
  · exact hExpandFace
  · exact hLRadiusEdge
  · exact hLRadiusFace
  · exact hThresholdEdge
  · exact hThresholdFace
end QEC.Coding.TannerLiftedProduct
