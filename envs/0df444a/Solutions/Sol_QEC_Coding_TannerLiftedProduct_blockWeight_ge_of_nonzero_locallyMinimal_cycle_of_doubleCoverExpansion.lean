-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.blockWeight_ge_of_nonzero_locallyMinimal_cycle_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:44:27.146129+00:00
-- url     : https://prove2.me/submissions/cbe32b18-4f00-4530-9636-1eac47cdf3a0

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cycle_eq_zero_of_doubleCoverExpansion

section
namespace QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
private theorem blockWeight_radius_bounds
    (weight radius degree : Nat)
    (hSmall : weight < radius / (2 * degree) + 1) :
    degree * weight ≤ radius ∧
      weight ≤ radius ∧
      weight ≤ radius / (2 * degree) := by
  have hFace : weight ≤ radius / (2 * degree) := by omega
  refine ⟨?_, hFace.trans (Nat.div_le_self radius _), hFace⟩
  calc
    degree * weight ≤ degree * (radius / (2 * degree)) :=
      Nat.mul_le_mul_left degree hFace
    _ ≤ (2 * degree) * (radius / (2 * degree)) := by
      exact Nat.mul_le_mul_right (radius / (2 * degree)) (by omega)
    _ ≤ radius := Nat.mul_div_le radius (2 * degree)
end QEC.Coding.TannerLiftedProduct
end

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
    (hcCycle : c ∈ (chainComplex label h g').middleCycleCode.carrier)
    (hcNonzero : c ≠ 0)
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
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    radius / (2 * Fintype.card W) + 1 ≤ blockWeight c := by
  by_contra hBound
  have hSmall : blockWeight c < radius / (2 * Fintype.card W) + 1 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨hVertical, hEdge, hFace⟩ :=
    blockWeight_radius_bounds (blockWeight c) radius (Fintype.card W) hSmall
  apply hcNonzero
  apply cycle_eq_zero_of_doubleCoverExpansion label h hRank g' gInjective c
  · exact ((chainComplex label h g').mem_middleCycleCode_iff c).1 hcCycle
  · exact hcLocal
  · exact hProductExpand
  · exact hDistance
  · exact hLength
  · exact hTwo
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact hBase
  · exact hVertical
  · exact hEdge
  · exact hFace
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold
end QEC.Coding.TannerLiftedProduct
