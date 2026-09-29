-- Prove2me | solution 1 for WorkbookSource.base_14689
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:34.782343+00:00
-- url     : https://prove2.me/submissions/66e8b466-65f5-4423-bd33-15abd0a14e7c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 39) * (a + 3 * b + c)^2  := by
  have hn : 0 ≤ (32*a^2 - 3*a*b - 14*a*c + 15*b^2 - 42*b*c + 32*c^2) := by
    have hs0 : 0 ≤ (32 : ℝ) * (1) * (-7*a/32 - 21*b/32 + c)^2 := by positivity
    have hs1 : 0 ≤ (975/32 : ℝ) * (1) * (a - b/5)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 39) * (a + 3 * b + c)^2) := @solution
#print axioms solution
