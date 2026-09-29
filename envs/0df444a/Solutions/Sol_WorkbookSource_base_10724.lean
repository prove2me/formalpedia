-- Prove2me | solution 1 for WorkbookSource.base_10724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:33.922589+00:00
-- url     : https://prove2.me/submissions/6a1bca02-cddc-48c7-b62a-c8df7a24fa89

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {x y z : ℝ} : (x^2 + x*y + y^2)*(z^2 + y^2 + y*z)*(z*x + x^2 + z^2) ≥ (z*x + x*y + y*z)^3  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^2*y/2 - x^2*z/2 - x*y^2/2 + x*z^2/2 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-x^2*y/2 - x^2*z/2 + x*y^2/2 - x*z^2/2 + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (-x^2*y + x*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 : ℝ) * (-x^2*z + x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ {x y z : ℝ}, (x^2 + x*y + y^2)*(z^2 + y^2 + y*z)*(z*x + x^2 + z^2) ≥ (z*x + x*y + y*z)^3) := @solution
#print axioms solution
