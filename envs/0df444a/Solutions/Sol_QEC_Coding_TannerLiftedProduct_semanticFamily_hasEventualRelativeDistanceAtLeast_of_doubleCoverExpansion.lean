-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRelativeDistanceAtLeast_of_doubleCoverExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:18:57.584309+00:00
-- url     : https://prove2.me/submissions/eef03491-66f9-446f-b441-5610f104b792

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_finrank_middleHomology_pos_of_local_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticPresentation_distance_ge_of_doubleCoverExpansion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
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
    (radius : A → Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : ∀ a, SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (label a)) (radius a) lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (relativeDistance : ℝ)
    (hRelative : ∀ a,
      relativeDistance * ((semanticPresentation (label a) h h').blockLength : ℝ) ≤
        (radius a / (2 * Fintype.card W) + 1 : Nat)) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (semanticFamily label h h' hW hGroupCofinal) relativeDistance := by
  refine ⟨0, ?_⟩
  intro a _ha
  change relativeDistance *
      ((semanticPresentation (label a) h h').blockLength : ℝ) ≤
    ((semanticPresentation (label a) h h').distance : ℝ)
  have hSemantic := semanticPresentation_distance_ge_of_doubleCoverExpansion
    (label a) h h' hRank h'Rank
    d m s beta hProductExpand hProductExpandReverse hDistance hDistanceReverse
    hLength hTwo hFour hDistanceScale hRectangleScale hBudget
    (radius a) lambda hLambda (hBase a)
    hVerticalThreshold hEdgeThreshold hFaceThreshold
    (finrank_middleHomology_pos_of_local_ratio
      (label a) h h' rate hRatePositive hW hRatio)
  have hSemanticReal :
      ((radius a / (2 * Fintype.card W) + 1 : Nat) : ℝ) ≤
        ((semanticPresentation (label a) h h').distance : ℝ) := by
    exact_mod_cast hSemantic
  exact (hRelative a).trans hSemanticReal
end QEC.Coding.TannerLiftedProduct
