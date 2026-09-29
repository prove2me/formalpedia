-- Prove2me | solution 1 for WorkbookSource.base_4009
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:58.935909+00:00
-- url     : https://prove2.me/submissions/238dc5ed-fd04-42dc-a421-38d4f1ce414d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (b^2 + c^2 + d^2 + a^2)^2 ≥ (c^2 * b + c * d^2 + a^2 * d + b^2 * a) * (a + b + c + d)  := by
  have h0 : 0 ≤ (1 : ℝ) * (a^2/5 - a*b/2 - 3*a*c/5 + 3*b^2/5 - 2*b*c/5 + c^2/5 - c*d/2 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (24/25 : ℝ) * (7*a^2/12 - 5*a*b/16 + a*c/8 - 25*a*d/48 + b^2/12 - 7*b*c/16 - 5*b*d/8 + c^2 + 5*c*d/48)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (19/30 : ℝ) * (a^2/19 - 21*a*b/76 - 15*a*c/38 - 43*a*d/76 + b^2 + 33*b*c/76 + 3*b*d/38 - 25*c*d/76)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (12/19 : ℝ) * (a^2 + 9*a*b/20 + a*c/10 - 3*a*d/10 - 3*b*c/10 - 2*b*d/5 - 11*c*d/20)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (8/25 : ℝ) * (-a*b/2 - 7*a*c/8 + 7*a*d/16 + 7*b*c/16 + b*d - c*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (3/40 : ℝ) * (a*c - a*d/2 - b*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c d : ℝ), (b^2 + c^2 + d^2 + a^2)^2 ≥ (c^2 * b + c * d^2 + a^2 * d + b^2 * a) * (a + b + c + d)) := @solution
#print axioms solution
