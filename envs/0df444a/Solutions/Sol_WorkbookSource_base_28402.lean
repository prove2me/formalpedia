-- Prove2me | solution 1 for WorkbookSource.base_28402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:45.936382+00:00
-- url     : https://prove2.me/submissions/62a2bb71-8db6-479f-a3aa-3f0a3c7d1736

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 10 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) + 120 * a^2 * b^2 * c^2 - 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 ≥ 0  := by
  have h0 : 0 ≤ (128 : ℝ) * (-a^2*b/8 - a^2*c/8 - a*b^2/8 + a*b*c - a*c^2/8 - b^2*c/8 - b*c^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (5 : ℝ) * (-a^2*b + a^2*c + a*b^2 - a*c^2 - b^2*c + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), 10 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) + 120 * a^2 * b^2 * c^2 - 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 ≥ 0) := @solution
#print axioms solution
