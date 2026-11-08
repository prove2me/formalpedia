-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.blockWeight_ge_of_nonzero_locallyMinimal_cocycle_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:11:23.229073+00:00
-- url     : https://prove2.me/submissions/e2e20fcc-d61e-4bcc-84d8-4d64b905b13b

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cocycle_eq_zero_of_doubleCoverExpansion
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
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h'.rank = Fintype.card R')
    (hInjective : Function.Injective
      (fun u : Word F R => h.transpose.mulVec u))
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzCocycle : z ∈ (chainComplex label h h').middleCocycleCode.carrier)
    (hzNonzero : z ≠ 0)
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
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
        (8 * lambda ^ 2)) ≤ s) :
    radius / (2 * Fintype.card W) + 1 ≤ blockWeight z := by
  by_contra hBound
  have hSmall : blockWeight z < radius / (2 * Fintype.card W) + 1 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨hVertical, hEdge, hFace⟩ :=
    blockWeight_radius_bounds (blockWeight z) radius (Fintype.card W) hSmall
  apply hzNonzero
  apply cocycle_eq_zero_of_doubleCoverExpansion label h h' hRank hInjective z
  · exact hzCocycle
  · exact hzLocal
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
