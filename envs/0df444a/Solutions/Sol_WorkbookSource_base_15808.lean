-- Prove2me | solution 1 for WorkbookSource.base_15808
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:35.441196+00:00
-- url     : https://prove2.me/submissions/b43968bd-5b88-41d6-b6ec-d668e28a9167

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a / b + b / c + c / a) + 1 ≥ 21 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2  := by
  have hn : 0 ≤ (2*a^4*c + 2*a^3*b^2 - 16*a^3*b*c + 4*a^3*c^2 + 4*a^2*b^3 + 8*a^2*b^2*c + 8*a^2*b*c^2 + 2*a^2*c^3 + 2*a*b^4 - 16*a*b^3*c + 8*a*b^2*c^2 - 16*a*b*c^3 + 2*b^3*c^2 + 4*b^2*c^3 + 2*b*c^4) := by
    have hs0 : 0 ≤ (8 : ℝ) * (c) * (a^2/2 - a*b - a*c/2 + b*c)^2 := by positivity
    have hs1 : 0 ≤ (8 : ℝ) * (b) * (-a*b + a*c + b*c/2 - c^2/2)^2 := by positivity
    have hs2 : 0 ≤ (8 : ℝ) * (a) * (a*b/2 - a*c - b^2/2 + b*c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 * (a / b + b / c + c / a) + 1 ≥ 21 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2) := @solution
#print axioms solution
