-- Prove2me | solution 2 for WeakGoldbach.symmetric_pair_count_pos_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T02:57:33.360624+00:00
-- url     : https://prove2.me/submissions/5c7b7842-570c-45ed-a335-939ce373b6d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_symmetric_pair_main_term_above_2e18
import Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one

theorem _root_.solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    0 < ((Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  have hmR : (2 * 10 ^ 18 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hL : 0 < Real.log m := Real.log_pos hm1
  have hS : (1 : ℝ) ≤ ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    WeakGoldbach.singular_series_factor_ge_one (2 * m)
  have hmain := WeakGoldbach.symmetric_pair_main_term_above_2e18 m hm
  have hpos : (0 : ℝ) <
      (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
        * (m : ℝ) / (Real.log m) ^ 2 := by
    apply div_pos _ (by positivity)
    nlinarith [hS, hm1]
  have := lt_of_lt_of_le hpos hmain
  exact_mod_cast this

#print axioms solution
