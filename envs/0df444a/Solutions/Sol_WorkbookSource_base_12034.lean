-- Prove2me | solution 1 for WorkbookSource.base_12034
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:48.434762+00:00
-- url     : https://prove2.me/submissions/fb80d42b-c3f8-49d5-834a-1fed1709cd1c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 4 * (a + b + 1) + (a - b) ^ 2 ≤ (a + b + 1) * (a + 1) ^ 2 * (b + 1) ^ 2 / (4 * a * b)  := by
  have hn : 0 ≤ (a^3*b^2 - 2*a^3*b + a^3 + a^2*b^3 + 13*a^2*b^2 - 9*a^2*b + 3*a^2 - 2*a*b^3 - 9*a*b^2 - 8*a*b + 3*a + b^3 + 3*b^2 + 3*b + 1) := by
    have hs0 : 0 ≤ (9 : ℝ) * (1) * (a*b - a/3 - b/3 - 1/3)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b) * (-a*b - a + b + 1)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a) * (-a*b + a - b + 1)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), 4 * (a + b + 1) + (a - b) ^ 2 ≤ (a + b + 1) * (a + 1) ^ 2 * (b + 1) ^ 2 / (4 * a * b)) := @solution
#print axioms solution
