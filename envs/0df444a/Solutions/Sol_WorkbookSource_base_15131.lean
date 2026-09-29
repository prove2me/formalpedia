-- Prove2me | solution 1 for WorkbookSource.base_15131
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:40.681284+00:00
-- url     : https://prove2.me/submissions/9db9eb1f-7d26-453a-bb94-a997bcd3ec7e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 23 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 18 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 9 * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2)  := by
  have h0 : 0 ≤ (27 : ℝ) * (a^2/3 - a*b/2 - a*c/2 - b^2/3 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (81/4 : ℝ) * (2*a^2/9 - a*b + a*c + 2*b^2/9 - 4*c^2/9)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 23 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 18 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 9 * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2)) := @solution
#print axioms solution
