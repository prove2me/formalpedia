-- Prove2me | solution 1 for WorkbookSource.base_12960
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:12.910541+00:00
-- url     : https://prove2.me/submissions/5bf3e771-f534-4606-a1d8-4f06bb8de236

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 8 * x ^ 3 * y + y ^ 3 + 2 * x ≥ 2 * x * y * (2 * x + y + 1)  := by
  have h0 : 0 ≤ (4 : ℝ) * (y) * (x - y/2)^2 := by positivity
  have h1 : 0 ≤ (2 : ℝ) * (x) * (1 - y)^2 := by positivity
  have h2 : 0 ≤ (8 : ℝ) * (x*y) * (x - 1/2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y), 8 * x ^ 3 * y + y ^ 3 + 2 * x ≥ 2 * x * y * (2 * x + y + 1)) := @solution
#print axioms solution
