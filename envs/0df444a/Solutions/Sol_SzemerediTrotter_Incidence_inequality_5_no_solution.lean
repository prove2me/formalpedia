-- Prove2me | solution 1 for SzemerediTrotter.Incidence.inequality_5_no_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:52:24.758092+00:00
-- url     : https://prove2.me/submissions/1ba25140-b89d-44a7-be0e-4c3a2a83e151

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

private theorem cube_two_thirds (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = x ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem cube_scaled_two_thirds (x : ℝ) (hx : 0 ≤ x) :
    ((2 : ℝ) ^ (-(1 / 3) : ℝ) * x ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = x ^ 2 / 2 := by
  have hc : ((2 : ℝ) ^ (-(1 / 3) : ℝ)) ^ (3 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  rw [mul_pow, hc, cube_two_thirds x hx]
  ring

theorem solution :
    (∀ x : ℝ, 0 < x → x ≤ 0.1 →
      x ^ (2 / 3 : ℝ) + (1 - x) / 100 + (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1 - x) ^ (2 / 3 : ℝ) ≤ 1) ∧
    (∃ x : ℝ, 0.1 < x ∧ x < 0.2 ∧
      1 < x ^ (2 / 3 : ℝ) + (1 - x) / 100 + (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1 - x) ^ (2 / 3 : ℝ)) := by
  constructor
  · intro x hx hx1
    have hcA := cube_two_thirds x hx.le
    have hcB := cube_scaled_two_thirds (1-x) (by linarith)
    by_cases hx5 : x ≤ 0.05
    · have hA : x ^ (2 / 3 : ℝ) ≤ 0.14 := by
        apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
        rw [hcA]
        have hs := pow_le_pow_left₀ hx.le hx5 2
        norm_num at hs ⊢
        linarith
      have hB : (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1-x) ^ (2 / 3 : ℝ) ≤ 0.8 := by
        apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
        rw [hcB]
        have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 1) 2
        norm_num at hs ⊢
        nlinarith
      linarith
    · have hA : x ^ (2 / 3 : ℝ) ≤ 0.22 := by
        apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
        rw [hcA]
        have hs := pow_le_pow_left₀ hx.le hx1 2
        norm_num at hs ⊢
        linarith
      have hB : (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1-x) ^ (2 / 3 : ℝ) ≤ 0.77 := by
        apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
        rw [hcB]
        have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 0.95) 2
        norm_num at hs ⊢
        nlinarith
      linarith
  · refine ⟨3/16, by norm_num, by norm_num, ?_⟩
    have hA0 : 0 ≤ (3/16 : ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have hcA := cube_two_thirds (3/16 : ℝ) (by norm_num)
    have hA : (0.32 : ℝ) < (3/16 : ℝ) ^ (2/3 : ℝ) := by
      apply lt_of_pow_lt_pow_left₀ (n := 3) hA0
      rw [hcA]
      norm_num
    have hcB := cube_scaled_two_thirds (1-(3/16) : ℝ) (by norm_num)
    have hB : (0.69 : ℝ) < (2 : ℝ) ^ (-(1/3) : ℝ) * (1-(3/16)) ^ (2/3 : ℝ) := by
      apply lt_of_pow_lt_pow_left₀ (n := 3) (mul_nonneg
        (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))
      rw [hcB]
      norm_num
    linarith
