-- Prove2me | solution 1 for QCircMITM.Search.sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:18:19.245984+00:00
-- url     : https://prove2.me/submissions/35bb6941-a332-423e-8616-c14515098acc

import Mathlib

theorem solution (m : ℕ) (hm : 2 ≤ m) (h : ℕ) :
    ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i * Real.logb 2 ((m : ℝ) ^ i) ≤
        ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i * Real.logb 2 ((m : ℝ) ^ h) ∧
      ∑ i ∈ Finset.Icc 1 h, (m : ℝ) ^ i ≤ (m : ℝ) ^ h * (1 + 1 / ((m : ℝ) - 1)) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    have hih : i ≤ h := (Finset.mem_Icc.1 hi).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact pow_le_pow_right₀ hm1 hih
  · have geo : ∀ k : ℕ, ((m : ℝ) - 1) * ∑ i ∈ Finset.Icc 1 k, (m : ℝ) ^ i =
        (m : ℝ) ^ (k + 1) - m := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
        ring
    have hpos : (0 : ℝ) < m - 1 := by linarith
    have hS := geo h
    have : (m : ℝ) ^ h * (1 + 1 / ((m : ℝ) - 1)) = (m : ℝ) ^ (h + 1) / ((m : ℝ) - 1) := by
      field_simp
      ring
    rw [this, le_div_iff₀ hpos, mul_comm, hS]
    linarith
