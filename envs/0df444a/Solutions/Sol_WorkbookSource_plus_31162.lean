-- Prove2me | solution 1 for WorkbookSource.plus_31162
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:45.338271+00:00
-- url     : https://prove2.me/submissions/7501215f-6652-40df-9067-ee88d663233c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 3 * a * b * c * (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) - 3 * a * b * c)   := by
  have h0 : 0 ≤ (1 : ℝ) * (b*c) * (a^2 - a*b - a*c + b*c)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (a*c) * (a*b - a*c - b^2 + b*c)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (a*b) * (a*b - a*c - b*c + c^2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 3 * a * b * c * (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) - 3 * a * b * c)) := @solution
#print axioms solution
