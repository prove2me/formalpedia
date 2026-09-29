-- Prove2me | solution 1 for WorkbookSource.base_14253
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:38.880341+00:00
-- url     : https://prove2.me/submissions/29d4a95e-c79c-4444-b10b-df15ee82e1a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 3 * a * b * c * (a + b + c) ≥ a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2)  := by
  have h0 : 0 ≤ (3 : ℝ) * (-5*a^2/27 + 23*a*b/54 - a*c/6 - 5*b^2/27 - b*c/6 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (704/243 : ℝ) * (-5*a^2/22 - a*b/11 + 9*a*c/22 + b^2 - 9*b*c/44)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (272/99 : ℝ) * (a^2 - 2*a*b/17 - 2*a*c/17 + 13*b*c/34)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (103/204 : ℝ) * (a*b + a*c + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 3 * a * b * c * (a + b + c) ≥ a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2)) := @solution
#print axioms solution
