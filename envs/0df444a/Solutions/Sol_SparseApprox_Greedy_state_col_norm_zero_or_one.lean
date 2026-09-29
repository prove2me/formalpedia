-- Prove2me | solution 1 for SparseApprox.Greedy.state_col_norm_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T22:41:52.934896+00:00
-- url     : https://prove2.me/submissions/01f65da9-8a38-41d4-a520-c4904f42fe0e

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace
open SparseApprox.Greedy

private lemma normalizeVec_eq_zero_or_norm_eq_one {m : ℕ}
    (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec v = 0 ∨ ‖normalizeVec v‖ = 1 := by
  by_cases hv : v = 0
  · left
    simp [normalizeVec, hv]
  · right
    have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [normalizeVec, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hnorm

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n)
    (r : ℕ) (j : Fin n) :
    (greedyState A b k r).col j = 0 ∨
      ‖(greedyState A b k r).col j‖ = 1 := by
  induction r with
  | zero =>
      simpa [greedyState, initState] using
        normalizeVec_eq_zero_or_norm_eq_one (colE A j)
  | succ r ih =>
      by_cases hj :
          j = k r ∨ j ∈ (greedyState A b k r).chosen
      · simpa [greedyState, greedyStep, hj] using ih
      · simpa [greedyState, greedyStep, hj] using
          normalizeVec_eq_zero_or_norm_eq_one
            ((greedyState A b k r).col j -
              ⟪(greedyState A b k r).col (k r),
                (greedyState A b k r).col j⟫_ℝ •
                (greedyState A b k r).col (k r))
