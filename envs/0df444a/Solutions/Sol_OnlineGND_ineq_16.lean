-- Prove2me | solution 1 for OnlineGND.ineq_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:39:25.570458+00:00
-- url     : https://prove2.me/submissions/aadf6d72-e249-40dd-8de6-e097d4f9cc2a

import Mathlib

theorem solution (α X Y : ℝ) (hα : 1 ≤ α) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (X + Y) ^ (α - 1) ≤ Real.exp 1 * X ^ (α - 1) + α ^ (α - 1) * Y ^ (α - 1) := by
  have hβ : 0 ≤ α - 1 := by linarith
  have hXb : 0 ≤ X ^ (α - 1) := Real.rpow_nonneg hX _
  have hYb : 0 ≤ α ^ (α - 1) * Y ^ (α - 1) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hY _)
  have he : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1; linarith
  rcases le_or_gt X ((α - 1) * Y) with h | h
  · have h1 : X + Y ≤ α * Y := by linarith
    have h2 : (X + Y) ^ (α - 1) ≤ (α * Y) ^ (α - 1) :=
      Real.rpow_le_rpow (by linarith) h1 hβ
    rw [Real.mul_rpow (by linarith) hY] at h2
    have : 0 ≤ Real.exp 1 * X ^ (α - 1) := mul_nonneg (by linarith) hXb
    linarith
  · rcases eq_or_lt_of_le hβ with h0 | hpos
    · rw [← h0]; simp only [Real.rpow_zero]
      nlinarith
    · have hY' : Y ≤ X / (α - 1) := by
        rw [le_div_iff₀ hpos]; linarith
      have h1 : X + Y ≤ X * (1 + 1 / (α - 1)) := by
        have : X / (α - 1) = X * (1 / (α - 1)) := by ring
        nlinarith
      have hb : 0 ≤ 1 + 1 / (α - 1) := by positivity
      have h2 : (X + Y) ^ (α - 1) ≤ (X * (1 + 1 / (α - 1))) ^ (α - 1) :=
        Real.rpow_le_rpow (by linarith) h1 hβ
      rw [Real.mul_rpow hX hb] at h2
      have h3 : (1 + 1 / (α - 1)) ^ (α - 1) ≤ Real.exp 1 := by
        have hle : 1 + 1 / (α - 1) ≤ Real.exp (1 / (α - 1)) := by
          have := Real.add_one_le_exp (1 / (α - 1)); linarith
        calc (1 + 1 / (α - 1)) ^ (α - 1) ≤ Real.exp (1 / (α - 1)) ^ (α - 1) :=
              Real.rpow_le_rpow hb hle hβ
          _ = Real.exp 1 := by
              rw [← Real.exp_mul, div_mul_cancel₀ (1 : ℝ) hpos.ne']
      have h4 : X ^ (α - 1) * (1 + 1 / (α - 1)) ^ (α - 1) ≤ X ^ (α - 1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left h3 hXb
      linarith
