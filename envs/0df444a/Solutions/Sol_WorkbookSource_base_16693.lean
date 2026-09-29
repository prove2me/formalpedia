-- Prove2me | solution 1 for WorkbookSource.base_16693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:37.820517+00:00
-- url     : https://prove2.me/submissions/3bc11870-6d42-4fed-ae0d-5cc27bad3f63

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b - c * a ≥ (5 / 32) * (a + 3 * b + c)^2  := by
  have hn : 0 ≤ (27*a^2 + 2*a*b - 42*a*c + 19*b^2 - 30*b*c + 27*c^2) := by
    have hs0 : 0 ≤ (27 : ℝ) * (1) * (-7*a/9 - 5*b/9 + c)^2 := by positivity
    have hs1 : 0 ≤ (32/3 : ℝ) * (1) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 + 2 * b^2 + c^2 + a * b - c * a ≥ (5 / 32) * (a + 3 * b + c)^2) := @solution
#print axioms solution
