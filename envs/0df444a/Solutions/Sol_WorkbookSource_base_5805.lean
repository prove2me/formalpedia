-- Prove2me | solution 1 for WorkbookSource.base_5805
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:59.61033+00:00
-- url     : https://prove2.me/submissions/1e11b0b2-25d6-485c-b651-d714e98536de

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) :
  (x^2 - x + 1) * (y^2 - y + 1) * (z^2 - z + 1) ≥ (x - y) * (y - z) * (z - x)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x*y*z/2 + x*y/2 + x*z/2 - x/2 + y*z/2 - y/2 - z/2 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (x*y*z/3 + x*y/3 + x*z/3 - x/3 - y*z - y/3 + z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2/3 : ℝ) * (x*y*z/2 - x*y + x*z/2 - x/2 + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 : ℝ) * (x*y*z - x*z + x)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (x y z : ℝ), (x^2 - x + 1) * (y^2 - y + 1) * (z^2 - z + 1) ≥ (x - y) * (y - z) * (z - x)) := @solution
#print axioms solution
