-- Prove2me | solution 1 for WorkbookSource.base_7388
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:41:01.258246+00:00
-- url     : https://prove2.me/submissions/24571f02-06b9-436b-a514-7250abfb4a90

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 8 * (a^2 - b * c) * (b^2 - c * a) * (c^2 - a * b) ≤ (a^2 + b^2 + c^2)^3  := by
  have h0 : 0 ≤ (20/3 : ℝ) * (-17*a^3/60 + a^2*b/20 + a^2*c/20 + a*b^2/20 + a*b*c + a*c^2/20 - 17*b^3/60 + b^2*c/20 + b*c^2/20 - 17*c^3/60)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (617/180 : ℝ) * (177*a^3/617 - 23*a^2*b/617 - 223*a^2*c/617 - 223*a*b^2/617 - 383*a*c^2/617 - 23*b^3/617 + 577*b^2*c/617 + b*c^2 + 17*c^3/617)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2112/617 : ℝ) * (91*a^3/2376 + a^2*b - 503*a^2*c/792 + 731*a*b^2/792 - 305*a*c^2/792 - 23*b^3/594 - 259*b^2*c/792 + 685*c^3/2376)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (475/297 : ℝ) * (a^3/3 + a^2*c + a*b^2/5 + a*c^2 + 8*b^3/15 + b^2*c/5 + c^3/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), 8 * (a^2 - b * c) * (b^2 - c * a) * (c^2 - a * b) ≤ (a^2 + b^2 + c^2)^3) := @solution
#print axioms solution
