-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_distance_and_productExpanding_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:22:59.325616+00:00
-- url     : https://prove2.me/submissions/c3b7dabb-da0e-42f1-8c12-14bd39f36541

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
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
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  obtain ⟨h, hKernelDistance, hNoBad⟩ :=
    exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
      (R := R) h' d s m k hDistanceFactor hRectangleFactor
  have hDistance := parityCheckCode_distance_of_mulVec_distance h d hKernelDistance
  exact ⟨h, hDistance,
    productExpanding_of_no_ranked_sparse_exactRectangle_witness
      h h' d m s k hPositive hLength hSmallM hRankTarget
        hDistance hDistance' hNoBad⟩
end QEC.Coding.ProductExpansion
