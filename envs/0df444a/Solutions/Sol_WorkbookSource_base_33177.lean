-- Prove2me | solution 1 for WorkbookSource.base_33177
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:08.390453+00:00
-- url     : https://prove2.me/submissions/1748397b-dee0-454e-b883-55818514ec2a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (a^2 + a * b + b^2 + b * c + c^2 + c * d + d^2 + d * a)^2 ≥ 2 * (a + b + c + d) * (a * b * (a + b) + b * c * (b + c) + c * d * (c + d) + d * a * (d + a))  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a^2 + b^2 - c^2 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (a*b - a*d - b*c + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c d : ℝ), (a^2 + a * b + b^2 + b * c + c^2 + c * d + d^2 + d * a)^2 ≥ 2 * (a + b + c + d) * (a * b * (a + b) + b * c * (b + c) + c * d * (c + d) + d * a * (d + a))) := @solution
#print axioms solution
