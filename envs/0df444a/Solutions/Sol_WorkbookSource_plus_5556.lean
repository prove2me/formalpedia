-- Prove2me | solution 1 for WorkbookSource.plus_5556
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:20.540508+00:00
-- url     : https://prove2.me/submissions/ca9e4164-3861-4465-a1c8-2c6a31bd2b2c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (3 * a ^ 2 - a * b + 3 * b ^ 2) * (3 * b ^ 2 - b * c + 3 * c ^ 2) * (3 * c ^ 2 - c * a + 3 * a ^ 2) ≥ 125 / 3 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)   := by
  have h0 : 0 ≤ (27 : ℝ) * (53*a^2*b/162 - a^2*c/9 - a*b^2/9 - 76*a*c^2/81 - b^2*c/6 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (80/3 : ℝ) * (-19*a^2*b/144 - a^2*c/8 + a*b^2 + 65*a*c^2/288 - 31*b^2*c/32)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (105/4 : ℝ) * (-17*a^2*b/18 + a^2*c - a*c^2/4 + 7*b^2*c/36)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (25/108 : ℝ) * (-a^2*b/2 - a*c^2/2 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (25/144 : ℝ) * (-a^2*b + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), (3 * a ^ 2 - a * b + 3 * b ^ 2) * (3 * b ^ 2 - b * c + 3 * c ^ 2) * (3 * c ^ 2 - c * a + 3 * a ^ 2) ≥ 125 / 3 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
