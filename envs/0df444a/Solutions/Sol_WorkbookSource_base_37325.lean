-- Prove2me | solution 1 for WorkbookSource.base_37325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:15.443429+00:00
-- url     : https://prove2.me/submissions/844a1ddd-2287-4b35-98d0-9239fea87a37

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c : ℝ} :
  4 * (a ^ 4 + b ^ 4 + c ^ 4) - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥
  (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3)  := by
  have h0 : 0 ≤ (3 : ℝ) * (-a^2/4 - a*b/6 - a*c/6 - b^2/4 - b*c/6 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (45/16 : ℝ) * (-a^2/3 - 2*a*b/9 - 2*a*c/9 + b^2 - 2*b*c/9)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (5/2 : ℝ) * (a^2 - a*b/3 - a*c/3 - b*c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ {a b c : ℝ}, 4 * (a ^ 4 + b ^ 4 + c ^ 4) - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥
  (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
