-- Prove2me | solution 1 for WorkbookSource.base_44753
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:24.439347+00:00
-- url     : https://prove2.me/submissions/c4b79923-a4b2-40f4-af2a-5d41a89f4aa1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)  := by
  have h0 : 0 ≤ (4 : ℝ) * (-x^2/14 + x*y/10 - x*z/4 - y^2/14 - y*z/4 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (195/49 : ℝ) * (-x^2/13 - 238*x*y/975 + 161*x*z/1950 + y^2 - 7*y*z/26)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (360/91 : ℝ) * (x^2 - 119*x*y/450 - 119*x*z/450 + 14*y*z/225)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (139/7875 : ℝ) * (28*x*y/139 + 28*x*z/139 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (6179/364875 : ℝ) * (28*x*y/167 + x*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (481/29225 : ℝ) * (x*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ), 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)) := @solution
#print axioms solution
