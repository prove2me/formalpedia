-- Prove2me | solution 1 for WorkbookSource.base_28649
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:06.064873+00:00
-- url     : https://prove2.me/submissions/15127b9a-2aaf-4e82-9af0-e115666adce8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) :  x^4 + y^4 + z^4 - (x + y + z) * x * y * z + (1 / 2) * y * z * (y - z)^2 ≥ 0  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^2/4 - x*y/4 - 3*y^2/4 + y*z/4 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (15/16 : ℝ) * (x^2 - x*y/15 - 7*y^2/15 - 7*y*z/15)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (x*z - y^2/2 - y*z/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (13/30 : ℝ) * (x*y - y^2/2 - y*z/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (x y z : ℝ), x^4 + y^4 + z^4 - (x + y + z) * x * y * z + (1 / 2) * y * z * (y - z)^2 ≥ 0) := @solution
#print axioms solution
