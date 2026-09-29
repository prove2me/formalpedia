-- Prove2me | solution 1 for WorkbookSource.base_45313
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:25.099576+00:00
-- url     : https://prove2.me/submissions/104ddfe3-8703-449e-9ea9-94b450b62135

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 9 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 10 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 2 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (10 : ℝ) * (3*a^2/10 - 2*a*b/5 - 2*a*c/5 - b^2/2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (42/5 : ℝ) * (a^2/7 - 2*a*b/3 + a*c + 5*b^2/42 - 25*c^2/42)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (14/3 : ℝ) * (-9*a^2/14 + a*b - 2*b^2/7 - c^2/14)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 9 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 10 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 2 * a * b * c * (a + b + c)) := @solution
#print axioms solution
