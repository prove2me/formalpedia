-- Prove2me | solution 1 for WorkbookSource.base_26943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:45.287276+00:00
-- url     : https://prove2.me/submissions/d7972595-b23d-49a7-adc4-0f9cbbfbd028

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 - 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  := by
  have h0 : 0 ≤ (2 : ℝ) * (a^3/2 - a^2*b/2 - a^2*c/2 - a*b^2/2 + b^3/2 - b^2*c/2 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/2 : ℝ) * (a^3/3 - a^2*b/3 - a^2*c/3 + a*b^2/3 - 2*a*c^2/3 + b^3 + b^2*c/3 - 2*b*c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (4/3 : ℝ) * (a^3 + a^2*b/2 + a^2*c/2 - a*b^2/2 - a*c^2/2 - b^2*c/2 - b*c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 - 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2) := @solution
#print axioms solution
