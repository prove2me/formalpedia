-- Prove2me | solution 1 for WorkbookSource.base_15265
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:17:00.502169+00:00
-- url     : https://prove2.me/submissions/51faf20e-ffea-4f28-9da5-bc93db3daf7f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) :
  (a^2 - 2 * a * b + c^2) * (a^2 + b * c) + (b^2 - 2 * b * c + d^2) * (b^2 + c * d) + (c^2 - 2 * c * d + a^2) * (c^2 + d * a) + (-2 * a * d + d^2 + b^2) * (d^2 + a * b) ≥ 0  := by
  have h0 : 0 ≤ (3/2 : ℝ) * (-a^2/3 + a*b/3 - a*c/3 - 2*a*d/3 + 2*b^2/3 - 2*b*c/3 + b*d/3 - 2*c^2/3 + c*d + d^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (4/3 : ℝ) * (-5*a^2/8 + a*b - a*c/4 - a*d/2 + b^2/8 - b*c/2 + b*d/4 - c^2/8 + 5*d^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3/4 : ℝ) * (a^2/2 - a*c - b^2/2 + b*d + c^2/2 - d^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 : ℝ) * (a^2/2 - a*d - b^2/2 + b*c - c^2/2 + d^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c d : ℝ), (a^2 - 2 * a * b + c^2) * (a^2 + b * c) + (b^2 - 2 * b * c + d^2) * (b^2 + c * d) + (c^2 - 2 * c * d + a^2) * (c^2 + d * a) + (-2 * a * d + d^2 + b^2) * (d^2 + a * b) ≥ 0) := @solution
#print axioms solution
