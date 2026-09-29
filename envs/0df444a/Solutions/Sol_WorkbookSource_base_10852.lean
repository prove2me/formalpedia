-- Prove2me | solution 1 for WorkbookSource.base_10852
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:35.088995+00:00
-- url     : https://prove2.me/submissions/32d2daca-3adb-470c-8c4c-74b9402d4f43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 27 * (x^2 + y^2) * (y^2 + z^2) * (z^2 + x^2) ≥ 8 * x * y * z * (x + y + z)^3  := by
  have h0 : 0 ≤ (27 : ℝ) * (x^2*y/27 - 4*x^2*z/9 - 4*x*y^2/9 - 4*x*z^2/27 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (27 : ℝ) * (-4*x^2*y/9 + x^2*z/27 - 4*x*y^2/27 - 4*x*z^2/9 + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (584/27 : ℝ) * (-21*x^2*y/146 + x^2*z - 58*x*y^2/73 - 9*x*z^2/146)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (41750/1971 : ℝ) * (x^2*y - 30*x*y^2/167 - 137*x*z^2/167)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1125/167 : ℝ) * (-x*y^2 + x*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ), 27 * (x^2 + y^2) * (y^2 + z^2) * (z^2 + x^2) ≥ 8 * x * y * z * (x + y + z)^3) := @solution
#print axioms solution
