-- Prove2me | solution 1 for WorkbookSource.plus_68450
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:49.158515+00:00
-- url     : https://prove2.me/submissions/7cb4fce4-ee20-4808-9e5a-c4298dd04781

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * a ^ 2 + 2 * b ^ 2 + c ^ 2 + 4 * a * b + 2 * c * (a + b) - 2 * (6 * a + 5 * b + 3 * c) + 14 ≥ 0   := by
  have h0 : 0 ≤ (14 : ℝ) * (1) * (-3*a/7 - 5*b/14 - 3*c/14 + 1)^2 := by positivity
  have h1 : 0 ≤ (3/7 : ℝ) * (1) * (a - b/3 - 2*c/3)^2 := by positivity
  have h2 : 0 ≤ (1/6 : ℝ) * (1) * (-b + c)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 * a ^ 2 + 2 * b ^ 2 + c ^ 2 + 4 * a * b + 2 * c * (a + b) - 2 * (6 * a + 5 * b + 3 * c) + 14 ≥ 0) := @solution
#print axioms solution
