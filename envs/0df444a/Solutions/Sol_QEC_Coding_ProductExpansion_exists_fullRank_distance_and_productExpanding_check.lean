-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_fullRank_distance_and_productExpanding_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:02.12096+00:00
-- url     : https://prove2.me/submissions/df8459b1-7212-43a7-b460-8b9f62ad0338

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_rank_eq_card_rows_of_image_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
import Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_distance_of_mulVec_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_productExpanding_of_no_ranked_sparse_exactRectangle_witness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
set_option maxHeartbeats 800000
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      h.rank = Fintype.card R ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, hKernelDistance, hImageDistance, hNoBad⟩ :=
    exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
      (R := R) h' d s m k hDistanceFactor hImageFactor hRectangleFactor
  have hDistance := parityCheckCode_distance_of_mulVec_distance
    h d hKernelDistance
  have hRank := rank_eq_card_rows_of_image_distance
    h d hPositive hImageDistance
  exact ⟨h, hRank, hDistance,
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h h' d m s k hPositive hLength hSmallM hRankTarget
        hDistance hDistance' hNoBad⟩
end QEC.Coding.ProductExpansion
