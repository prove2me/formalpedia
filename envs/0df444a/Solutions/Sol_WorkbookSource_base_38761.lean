-- Prove2me | solution 1 for WorkbookSource.base_38761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:18.580779+00:00
-- url     : https://prove2.me/submissions/1368a95a-46d7-4662-9bb3-de324107df6d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) :
  (x^3 + y^3 + z^3)^2 + 3 * (x * y * z)^2 ≥
    4 * (y^3 * z^3 + z^3 * x^3 + x^3 * y^3) + (x - y)^2 * (y - z)^2 * (z - x)^2  := by
  have h0 : 0 ≤ (3 : ℝ) * (x^3/3 - x^2*y/3 - x^2*z/3 - x*y^2/3 + x*y*z - x*z^2/3 + y^3/3 - y^2*z/3 - y*z^2/3 + z^3/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2/3 : ℝ) * (-x^3/2 + x^2*y/2 - x^2*z + x*y^2/2 + x*z^2/2 - y^3/2 - y^2*z + y*z^2/2 + z^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (x^3 + x^2*y - x*y^2 - x*z^2 - y^3 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), (x^3 + y^3 + z^3)^2 + 3 * (x * y * z)^2 ≥
    4 * (y^3 * z^3 + z^3 * x^3 + x^3 * y^3) + (x - y)^2 * (y - z)^2 * (z - x)^2) := @solution
#print axioms solution
