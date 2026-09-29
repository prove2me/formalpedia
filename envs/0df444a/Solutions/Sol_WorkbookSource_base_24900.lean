-- Prove2me | solution 1 for WorkbookSource.base_24900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:41.016649+00:00
-- url     : https://prove2.me/submissions/9b28c601-ea7a-48ee-bff5-2f19c961d063

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 3 * (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) ≥ a^3 * b^3 + b^3 * c^3 + c^3 * a^3  := by
  have h0 : 0 ≤ (3 : ℝ) * (a^2*b/6 - a*c^2/2 - 2*b^2*c/3 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-2*a^2*b/3 + a*b^2 + a*c^2/6 - b^2*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3 : ℝ) * (-a^2*b/2 + a^2*c - 2*a*c^2/3 + b^2*c/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (5/6 : ℝ) * (-a^2*b/2 - a*c^2/2 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (5/8 : ℝ) * (-a^2*b + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), 3 * (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) ≥ a^3 * b^3 + b^3 * c^3 + c^3 * a^3) := @solution
#print axioms solution
