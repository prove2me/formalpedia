-- Prove2me | solution 1 for WorkbookSource.base_24200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:17:03.598425+00:00
-- url     : https://prove2.me/submissions/d0c5e401-1d97-4616-b0e5-d5b990f50550

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c: ℝ) : (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ (4 / 7) * (a ^ 4 + b ^ 4 + c ^ 4)  := by
  have h0 : 0 ≤ (40/7 : ℝ) * (-a^2/10 + a*b/10 + a*c/10 + 7*b^2/20 + b*c + 7*c^2/20)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (198/35 : ℝ) * (4*a^2/11 + a*b/11 + a*c - 3*b^2/22 + 7*c^2/22)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (432/77 : ℝ) * (a^2/3 + a*b + b^2/3 - c^2/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c: ℝ), (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ (4 / 7) * (a ^ 4 + b ^ 4 + c ^ 4)) := @solution
#print axioms solution
