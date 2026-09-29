-- Prove2me | solution 1 for WorkbookSource.base_47874
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:27.484855+00:00
-- url     : https://prove2.me/submissions/9975c353-3117-46a6-b365-4f40025e8f39

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  3 * (a ^ 4 + b ^ 4 + c ^ 4) + 2 * (b ^ 3 * a + a ^ 3 * c + c ^ 3 * b) ≥
  3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  := by
  have h0 : 0 ≤ (3 : ℝ) * (-a^2/6 + a*b/6 - a*c/2 - b^2/6 + b*c/3 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (35/12 : ℝ) * (-a^2/5 + 13*a*b/35 + 3*a*c/35 + b^2 - 16*b*c/35)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (14/5 : ℝ) * (a^2 - 3*a*b/7 + 2*a*c/7 + b*c/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 2 * (b ^ 3 * a + a ^ 3 * c + c ^ 3 * b) ≥
  3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) := @solution
#print axioms solution
