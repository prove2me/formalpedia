-- Prove2me | solution 1 for WorkbookSource.base_30719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:06.922731+00:00
-- url     : https://prove2.me/submissions/2e5f477a-70ee-440e-a550-ef47e30f8d71

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (a^2 - a*b + b^2) * (c^2 - c*d + d^2) ≥ 2/3 * (a^2*c^2 - a*c*b*d + b^2*d^2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a*c/2 + a*d/2 + b*c - b*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (-a*c/3 + a*d - b*d/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c d : ℝ), (a^2 - a*b + b^2) * (c^2 - c*d + d^2) ≥ 2/3 * (a^2*c^2 - a*c*b*d + b^2*d^2)) := @solution
#print axioms solution
