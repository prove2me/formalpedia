-- Prove2me | solution 1 for WorkbookSource.base_3618
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:53.341469+00:00
-- url     : https://prove2.me/submissions/47b8f835-78dc-4d5a-b4b4-442fdab3246e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 32 * (x^2 + y^2) * (x^2 + z^2) + 32 * (y^2 + z^2) * (x^2 + y^2) + 32 * (x^2 + z^2) * (y^2 + z^2) ≥ (3 * x + y)^2 * (x + y) * (z + 2 * x + y) + (3 * y + z)^2 * (y + z) * (2 * y + z + x) + (3 * z + x)^2 * (z + x) * (2 * z + x + y)  := by
  have h0 : 0 ≤ (201/4 : ℝ) * (-x^2/67 - 41*x*y/201 - 41*x*z/201 - 80*y^2/201 + y*z - 12*z^2/67)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9680/201 : ℝ) * (-669*x^2/3520 - 41*x*y/160 + x*z - 353*y^2/3520 - 399*z^2/880)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (14399/320 : ℝ) * (-x^2/2 + x*y - 7*y^2/22 - 2*z^2/11)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), 32 * (x^2 + y^2) * (x^2 + z^2) + 32 * (y^2 + z^2) * (x^2 + y^2) + 32 * (x^2 + z^2) * (y^2 + z^2) ≥ (3 * x + y)^2 * (x + y) * (z + 2 * x + y) + (3 * y + z)^2 * (y + z) * (2 * y + z + x) + (3 * z + x)^2 * (z + x) * (2 * z + x + y)) := @solution
#print axioms solution
