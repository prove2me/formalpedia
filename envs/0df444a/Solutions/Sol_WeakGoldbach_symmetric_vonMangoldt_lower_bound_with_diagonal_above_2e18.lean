-- Prove2me | solution 1 for WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:29:11.047117+00:00
-- url     : https://prove2.me/submissions/84938911-0f03-453f-81ed-dd4a464e7395
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_off_diagonal_lower_bound_above_2e18

open WeakGoldbach

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (5 / 4 : ℝ) *
        (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ)
      + ((ArithmeticFunction.vonMangoldt m : ℝ) ^ 2) / 2
      ≤ ∑ t ∈ Finset.range (m - 1),
          (ArithmeticFunction.vonMangoldt (m - t) : ℝ) *
            (ArithmeticFunction.vonMangoldt (m + t) : ℝ) := by
  let F : ℕ → ℝ := fun t =>
    (ArithmeticFunction.vonMangoldt (m - t) : ℝ) *
      (ArithmeticFunction.vonMangoldt (m + t) : ℝ)
  have hzero : 0 ∈ Finset.range (m - 1) := by
    simp only [Finset.mem_range]
    omega
  have hsplit :
      F 0 + ∑ t ∈ (Finset.range (m - 1)).erase 0, F t =
        ∑ t ∈ Finset.range (m - 1), F t := by
    exact Finset.add_sum_erase (a := 0) _ _ hzero
  have hdiagonal : F 0 = (ArithmeticFunction.vonMangoldt m : ℝ) ^ 2 := by
    simp [F, pow_two]
  have hoff :=
    WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_above_2e18 m hm
  change
    (5 / 4 : ℝ) *
        (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ)
      ≤ ∑ t ∈ (Finset.range (m - 1)).erase 0, F t at hoff
  rw [← hsplit, hdiagonal]
  nlinarith [hoff, sq_nonneg (ArithmeticFunction.vonMangoldt m : ℝ)]
