-- Prove2me | solution 1 for WaitJudge.Convex.iteratedDeriv_pow_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:17:57.553347+00:00
-- url     : https://prove2.me/submissions/417927c1-0db7-45e0-83d5-e6101b80a2fc

import Mathlib

theorem solution (k m : ℕ) (t : ℝ) :
    (1 / (k.factorial : ℝ)) * iteratedDeriv k (fun t : ℝ => t ^ m) t =
      if m < k then 0 else (m.choose k : ℝ) * t ^ (m - k) := by
  rw [iteratedDeriv_pow]
  by_cases h : m < k
  · simp [h, Nat.descFactorial_eq_zero_iff_lt.mpr h]
  · simp only [h, if_false]
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp

#print axioms solution
