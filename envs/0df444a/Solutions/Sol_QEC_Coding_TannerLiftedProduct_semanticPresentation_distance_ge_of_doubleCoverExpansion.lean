-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.semanticPresentation_distance_ge_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:11.721268+00:00
-- url     : https://prove2.me/submissions/6621ca5b-748f-4a4c-bcbe-0cae0c338ce5

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_transpose_mulVec_injective_of_rank_eq_card_rows
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_le_semanticPresentation_distance
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
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
    (hHomologyPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology) :
    radius / (2 * Fintype.card W) + 1 ≤
      (semanticPresentation label h h').distance := by
  obtain ⟨dCSS, hMinimum⟩ :=
    exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
      label h h' hHomologyPositive
  have hInjective :=
    transpose_mulVec_injective_of_rank_eq_card_rows h hRank
  have h'Injective :=
    transpose_mulVec_injective_of_rank_eq_card_rows h' h'Rank
  exact (algebraicCSSMinimumDistance_ge_of_doubleCoverExpansion
    label h h' hRank h'Injective h'Rank hInjective
    d m s beta hProductExpand hProductExpandReverse
    hDistance hDistanceReverse hLength hTwo hFour hDistanceScale
    hRectangleScale hBudget radius lambda hLambda hBase
    hVerticalThreshold hEdgeThreshold hFaceThreshold dCSS hMinimum).trans
      (algebraicCSSMinimumDistance_le_semanticPresentation_distance
        label h h' dCSS hMinimum)
end QEC.Coding.TannerLiftedProduct
