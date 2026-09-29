-- Prove2me | solution 1 for WorkbookSource.base_7774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:41:02.214001+00:00
-- url     : https://prove2.me/submissions/53da7bc8-e429-4f91-8abd-c9177cf54d5c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : x^6 + y^6 + z^6 + 3 * x^2 * y^2 * z^2 ≥ 2 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^3/2 + x^2*y/2 - x^2*z/2 + x*y^2/2 - y^3/2 - y^2*z/2 + z^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (x^3/2 + x^2*y/2 - x^2*z/2 - x*y^2/2 - y^3/2 - y^2*z/2 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-x^3/2 - x^2*y/2 - x^2*z/2 + x*y^2/2 + x*z^2 + y^3/2 - y^2*z/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/4 : ℝ) * (x^3 - x^2*y - x^2*z + x*y^2 - y^3 + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (x y z : ℝ), x^6 + y^6 + z^6 + 3 * x^2 * y^2 * z^2 ≥ 2 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3)) := @solution
#print axioms solution
