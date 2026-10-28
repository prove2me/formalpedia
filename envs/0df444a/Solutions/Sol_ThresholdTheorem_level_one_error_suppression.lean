-- Prove2me | solution 1 for ThresholdTheorem.level_one_error_suppression
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:20:39.42531+00:00
-- url     : https://prove2.me/submissions/99cd9cde-1b31-4819-93da-3f2366a42257
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model
import Theorems.Thm_ThresholdTheorem_level_one_sparse_fault_correctness
import Theorems.Thm_ThresholdTheorem_tvDist_le_malignant_pairs

open ThresholdTheorem

theorem solution :
    ∃ (c A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2), 0 < c ∧
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * C.size ∧
        ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
          tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
            ≤ c * p ^ 2 * C.size := by
  obtain ⟨M, A, b, dec, h⟩ := ThresholdTheorem.level_one_sparse_fault_correctness
  refine ⟨max M 1, A, b, dec, by positivity, fun n C => ?_⟩
  obtain ⟨C', hsize, B, hcard, hdiag, hgood⟩ := h n C
  refine ⟨C', hsize, fun p hp hcp N => ?_⟩
  have hp1 : p ≤ 1 := by
    have : 1 * p ≤ max M 1 * p := mul_le_mul_of_nonneg_right (le_max_right _ _) hp
    linarith
  have key := ThresholdTheorem.tvDist_le_malignant_pairs dec C' B hdiag _ p hp1 N
    (fun N' _ h01 hB => hgood N' h01 hB)
  have hM : (B.card : ℝ) ≤ max M 1 * C.size :=
    hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  calc _ ≤ (B.card : ℝ) * p ^ 2 := key
    _ ≤ max M 1 * C.size * p ^ 2 := mul_le_mul_of_nonneg_right hM (sq_nonneg p)
    _ = max M 1 * p ^ 2 * C.size := by ring
