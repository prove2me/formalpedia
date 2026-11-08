-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cycle_eq_zero_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:39:02.945843+00:00
-- url     : https://prove2.me/submissions/53755228-7b39-4148-9f3b-f1a9ee145327

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_expanding_of_doubleCover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_expanding_of_doubleCover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_expanding_of_doubleCover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_globalExpansion_of_blockWeight


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
universe u
variable {F : Type u} {R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
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
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight c ≤ radius)
    (hBlockRadiusEdge : blockWeight c ≤ radius)
    (hBlockRadiusFace :
      blockWeight c ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    c = 0 := by
  exact cycle_eq_zero_of_globalExpansion_of_blockWeight
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
    hProductExpand hDistance hLength hTwo hFour hDistanceScale
    hRectangleScale hBudget
    radius lambda
    (verticalFaceGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    hBlockRadiusVertical hVerticalThreshold
    radius (radius / (2 * Fintype.card W))
    (2 * lambda)
    (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2))
    (by positivity) (by positivity)
    (adjacencyGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    (faceSquareGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    hBlockRadiusEdge hBlockRadiusFace hEdgeThreshold hFaceThreshold
end QEC.Coding.TannerLiftedProduct
