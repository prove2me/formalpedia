-- Prove2me | solution 1 for WorkbookSource.base_2640
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:09.905303+00:00
-- url     : https://prove2.me/submissions/c1561c4e-2723-449c-b4b5-d6fae1adbe35

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 9 * a ^ 2 * b + a ^ 2 * c + 9 * a * b ^ 2 + a * c ^ 2 + b ^ 2 * c + b * c ^ 2 ≥ 14 * a * b * c  := by
  have h0 : 0 ≤ (1 : ℝ) * (c) * (-a + b)^2 := by positivity
  have h1 : 0 ≤ (9 : ℝ) * (b) * (a - c/3)^2 := by positivity
  have h2 : 0 ≤ (9 : ℝ) * (a) * (b - c/3)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 9 * a ^ 2 * b + a ^ 2 * c + 9 * a * b ^ 2 + a * c ^ 2 + b ^ 2 * c + b * c ^ 2 ≥ 14 * a * b * c) := @solution
#print axioms solution
