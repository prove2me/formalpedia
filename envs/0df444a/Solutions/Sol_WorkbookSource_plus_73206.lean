-- Prove2me | solution 1 for WorkbookSource.plus_73206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:42.723116+00:00
-- url     : https://prove2.me/submissions/dae254a9-6f4a-4b1a-b412-032dc99ce451

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) + 3 * a * b * c * (a + b + c)   := by
  have h0 : 0 ≤ (15/4 : ℝ) * (-a^2/5 - a*b/5 - a*c/5 + b*c - 2*c^2/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (18/5 : ℝ) * (-11*a^2/24 - a*b/4 + a*c - 5*b^2/24 - c^2/12)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (27/8 : ℝ) * (-a^2/6 + a*b - b^2/2 - c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) + 3 * a * b * c * (a + b + c)) := @solution
#print axioms solution
