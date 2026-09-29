-- Prove2me | solution 1 for WorkbookSource.base_54653
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:31.944117+00:00
-- url     : https://prove2.me/submissions/2bad1c86-2e2e-484e-9c23-a51eed52e372

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 2 * (a^3 * b + b^3 * c + c^3 * a) + 11 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a * b^3 + b * c^3 + c * a^3) + 8 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (11 : ℝ) * (a^2/11 - 5*a*b/11 - 5*a*c/11 + b^2/11 + b*c - 3*c^2/11)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (96/11 : ℝ) * (-7*a^2/24 - 5*a*b/6 + a*c + b^2/6 - c^2/24)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (8/3 : ℝ) * (-a^2/4 + a*b - b^2/2 - c^2/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), a^4 + b^4 + c^4 + 2 * (a^3 * b + b^3 * c + c^3 * a) + 11 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a * b^3 + b * c^3 + c * a^3) + 8 * a * b * c * (a + b + c)) := @solution
#print axioms solution
