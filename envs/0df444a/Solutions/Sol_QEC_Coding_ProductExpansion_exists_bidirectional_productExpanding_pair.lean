-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_bidirectional_productExpanding_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:38.585663+00:00
-- url     : https://prove2.me/submissions/92e54910-7c77-4877-9edb-e0adc22830cd

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_bidirectional_local_pair_without_bad_events
import Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_distance_of_mulVec_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_generatorImageParityCheck_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_productExpanding_of_no_ranked_sparse_exactRectangle_witness
import Theorems.Thm_QEC_Coding_ProductExpansion_rank_eq_card_rows_of_image_distance


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
set_option maxHeartbeats 1200000
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
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
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R')) :
    ∃ (h : Matrix R W F) (g' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      g'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck h)).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode g').carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpanding g' (generatorImageParityCheck h) s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, g', hKernelDistance, hImageDistance,
      hKernelDistance', hImageDistance', hNoForward, hNoReverse⟩ :=
    exists_bidirectional_local_pair_without_bad_events
      (F := F) (W := W) (R := R) (R' := R') d s m k
      hFirstKernelFactor hFirstImageFactor hSecondKernelFactor
      hSecondImageFactor hForwardRectangleFactor hReverseRectangleFactor
  have hRank := rank_eq_card_rows_of_image_distance
    h d hPositive hImageDistance
  have hRank' := rank_eq_card_rows_of_image_distance
    g' d hPositive hImageDistance'
  have hCheckDistance := parityCheckCode_distance_of_mulVec_distance
    h d hKernelDistance
  have hCheckDistance' := parityCheckCode_distance_of_mulVec_distance
    g' d hKernelDistance'
  have hRowImageDistance := parityCheckCode_generatorImageParityCheck_distance
    h d hImageDistance
  have hRowImageDistance' := parityCheckCode_generatorImageParityCheck_distance
    g' d hImageDistance'
  have hForwardExpand :=
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h (generatorImageParityCheck g') d m s k
      hPositive hLength hSmallM hRankTarget
      hCheckDistance hRowImageDistance' hNoForward
  have hReverseExpand :=
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      g' (generatorImageParityCheck h) d m s k
      hPositive hLength hSmallM hRankTarget
      hCheckDistance' hRowImageDistance hNoReverse
  exact ⟨h, g', hRank, hRank', hCheckDistance, hRowImageDistance,
    hCheckDistance', hRowImageDistance', hForwardExpand, hReverseExpand⟩
end QEC.Coding.ProductExpansion
