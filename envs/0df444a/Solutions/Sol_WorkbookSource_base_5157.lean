-- Prove2me | solution 1 for WorkbookSource.base_5157
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:58.81923+00:00
-- url     : https://prove2.me/submissions/3760baa0-cc4b-4360-97db-84b007527cfb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 10 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b) + 9 * (a^4 + b^4 + c^4) + 11 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≥ 40 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (35/2 : ℝ) * (-5*a^2/7 - 3*a*b/7 - 3*a*c/7 + 2*b^2/7 + b*c + 2*c^2/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (100/7 : ℝ) * (-a^2/40 - 3*a*b/4 + a*c - 29*b^2/40 + c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (25/4 : ℝ) * (-a^2/10 + a*b - b^2/10 - 4*c^2/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 10 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b) + 9 * (a^4 + b^4 + c^4) + 11 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≥ 40 * a * b * c * (a + b + c)) := @solution
#print axioms solution
