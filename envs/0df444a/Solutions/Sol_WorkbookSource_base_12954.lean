-- Prove2me | solution 1 for WorkbookSource.base_12954
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:31.145809+00:00
-- url     : https://prove2.me/submissions/ffb83809-4bdd-410d-9c74-75186116b20c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c + 4 * (b * c / a + c * a / b + a * b / c) + a^2 / b + b^2 / c + c^2 / a ≥ 18 * (a^2 + b^2 + c^2) / (a + b + c)  := by
  have hn : 0 ≤ (a^4*c + 4*a^3*b^2 - 16*a^3*b*c + 5*a^3*c^2 + 5*a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 + 4*a^2*c^3 + a*b^4 - 16*a*b^3*c + 6*a*b^2*c^2 - 16*a*b*c^3 + 4*b^3*c^2 + 5*b^2*c^3 + b*c^4) := by
    have hs0 : 0 ≤ (9 : ℝ) * (c) * (a^2/3 - 2*a*b/3 - 2*a*c/3 + b*c)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (b) * (a*b - 2*a*c/3 - 2*b*c/3 + c^2/3)^2 := by positivity
    have hs2 : 0 ≤ (9 : ℝ) * (a) * (-2*a*b/3 + a*c + b^2/3 - 2*b*c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), a + b + c + 4 * (b * c / a + c * a / b + a * b / c) + a^2 / b + b^2 / c + c^2 / a ≥ 18 * (a^2 + b^2 + c^2) / (a + b + c)) := @solution
#print axioms solution
