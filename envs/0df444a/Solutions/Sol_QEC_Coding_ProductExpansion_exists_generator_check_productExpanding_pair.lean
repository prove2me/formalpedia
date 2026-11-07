-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_generator_check_productExpanding_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:59.99877+00:00
-- url     : https://prove2.me/submissions/e5e5a804-da9a-44b2-8192-bab2e5ab50fc

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_generator_with_image_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_generatorImageParityCheck_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_rank_eq_card_rows_of_image_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_distance_and_productExpanding_check

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
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hGeneratorFactor :
      (Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W)
    (hCheckDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ (g' : Matrix R' W F) (h : Matrix R W F),
      g'.rank = Fintype.card R' ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨g', hImage⟩ := exists_generator_with_image_distance
    (F := F) (W := W) (R := R') d hGeneratorFactor
  have hGeneratorRank :=
    rank_eq_card_rows_of_image_distance g' d hPositive hImage
  have hImageDistance :=
    parityCheckCode_generatorImageParityCheck_distance g' d hImage
  obtain ⟨h, hCheckDistance, hExpand⟩ :=
    exists_distance_and_productExpanding_check
      (R := R) (generatorImageParityCheck g') d s m k
      hPositive hLength hSmallM hRankTarget hImageDistance
      hCheckDistanceFactor hRectangleFactor
  exact ⟨g', h, hGeneratorRank, hImageDistance, hCheckDistance, hExpand⟩
end QEC.Coding.ProductExpansion
