-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:13:24.390914+00:00
-- url     : https://prove2.me/submissions/cc408d63-4053-4665-806e-dbda051d4beb

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_ge_of_nonzero_locallyMinimal_cycle_of_doubleCoverExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds


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
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Injective : Function.Injective
      (fun u : Word F R' => h'.transpose.mulVec u))
    (h'Rank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    radius / (2 * Fintype.card W) + 1 ≤ dCSS := by
  apply algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
    label h h' (radius / (2 * Fintype.card W) + 1) dCSS
  · intro c hcCycle hcNonzero hcLocal
    exact blockWeight_ge_of_nonzero_locallyMinimal_cycle_of_doubleCoverExpansion
      label h hRank h' h'Injective c hcCycle hcNonzero hcLocal
      d m s beta hProductExpand hDistance hLength hTwo hFour
      hDistanceScale hRectangleScale hBudget radius lambda hLambda hBase
      hVerticalThreshold hEdgeThreshold hFaceThreshold
  · intro z hzCocycle hzNonzero hzLocal
    exact blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
      label h h' h'Rank hInjective z hzCocycle hzNonzero hzLocal
      d m s beta hProductExpandReverse hDistanceReverse hLength hTwo hFour
      hDistanceScale hRectangleScale hBudget radius lambda hLambda hBase
      hVerticalThreshold hEdgeThreshold hFaceThreshold
  · exact hMinimum
end QEC.Coding.TannerLiftedProduct
