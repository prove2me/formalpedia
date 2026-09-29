-- Prove2me | solution 1 for WorkbookSource.base_1747
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:50.672412+00:00
-- url     : https://prove2.me/submissions/b2a65f9d-45e7-444c-8628-dc897dc44208

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : x ^ 2 * y ^ 2 + z ^ 4 + x ^ 4 + y ^ 4 + x * y ^ 3 ≥ z ^ 2 * (x ^ 2 + y ^ 2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^2/2 - y^2/2 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (8*x^2/75 + 2*x*y/3 + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (5561/7500 : ℝ) * (x^2 - 400*x*y/5561)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (787/278050 : ℝ) * (x*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (x y z : ℝ), x ^ 2 * y ^ 2 + z ^ 4 + x ^ 4 + y ^ 4 + x * y ^ 3 ≥ z ^ 2 * (x ^ 2 + y ^ 2)) := @solution
#print axioms solution
