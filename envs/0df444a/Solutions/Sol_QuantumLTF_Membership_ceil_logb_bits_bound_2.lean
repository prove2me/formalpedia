-- Prove2me | solution 2 for QuantumLTF.Membership.ceil_logb_bits_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T10:59:07.634118+00:00
-- url     : https://prove2.me/submissions/19d13b65-5aa5-4270-8e35-72929dc2afb8

import Mathlib

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ((4 + ⌈Real.logb 2 n⌉₊ : ℕ) : ℝ) ≤ C * Real.log n := by
  refine ⟨12, by norm_num, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (0 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlogle : Real.log 2 ≤ Real.log n :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hnpos hn2
  have hx : 0 ≤ Real.logb 2 n := by
    unfold Real.logb
    positivity
  have hceil : (⌈Real.logb 2 n⌉₊ : ℝ) < Real.logb 2 n + 1 :=
    Nat.ceil_lt_add_one hx
  have hxbound : Real.logb 2 n < 2 * Real.log n := by
    unfold Real.logb
    have hlogn : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogle
    have hdiv := (div_lt_iff₀ hlog2).2
      (show Real.log n < (2 * Real.log n) * Real.log 2 by nlinarith)
    exact hdiv
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith
