-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_localPair_with_semanticRateAndDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:34:15.56875+00:00
-- url     : https://prove2.me/submissions/80fb9353-382a-4fbe-b1b4-239f903d6d54

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_bidirectional_productExpanding_pair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_finrank_middleHomology_pos_of_local_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rate_le_semanticPresentation_encodedQudits_of_local_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticPresentation_distance_ge_of_doubleCoverExpansion


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_24
set_option maxHeartbeats 1200000
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G)
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * (2 * m) ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R'))
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
        ((semanticPresentation label h h').encodedQudits : ℝ) ∧
      radius / (2 * Fintype.card W) + 1 ≤
        (semanticPresentation label h h').distance := by
  obtain ⟨h, h', hRank, h'Rank, hDistance, _hImageDistance,
      hDistanceReverse, _hImageDistanceReverse,
      hProductExpand, hProductExpandReverse⟩ :=
    ProductExpansion.exists_bidirectional_productExpanding_pair
      (F := F) (W := W) (R := R) (R' := R')
      d s (2 * m) k hPositive hLength hSmallM hRankTarget
      hFirstKernelFactor hFirstImageFactor hSecondKernelFactor
      hSecondImageFactor hForwardRectangleFactor hReverseRectangleFactor
  have hRate :=
    rate_le_semanticPresentation_encodedQudits_of_local_ratio
      label h h' rate hRatio
  refine ⟨h, h', hRank, h'Rank, hRate, ?_⟩
  have hHomologyPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology :=
    finrank_middleHomology_pos_of_local_ratio
      label h h' rate hRatePositive (by omega) hRatio
  apply semanticPresentation_distance_ge_of_doubleCoverExpansion
    label h h' hRank h'Rank
    d m s ((d : ℝ) / (3 * (Fintype.card W : ℝ)))
  · exact hProductExpand
  · exact hProductExpandReverse
  · exact hDistance
  · exact hDistanceReverse
  · exact hLength
  · omega
  · exact hFour
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambda
  · exact hBase
  · exact hVerticalThreshold
  · exact hEdgeThreshold
  · exact hFaceThreshold
  · exact hHomologyPositive
end QEC.Coding.TannerLiftedProduct
