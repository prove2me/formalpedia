-- Prove2me | solution 1 for WorkbookSource.base_6624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:25.287057+00:00
-- url     : https://prove2.me/submissions/f059c559-3a70-4743-8bdd-8f7198f2125d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c) / (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 2 / (a + b + c) ≥ (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have hn : 0 ≤ (a^4*b^2 + a^4*b*c + a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by
    have hs0 : 0 ≤ (1 : ℝ) * (1) * (a^2*b/2 - a^2*c/2 - a*b^2/2 + a*c^2/2 - b^2*c + b*c^2)^2 := by positivity
    have hs1 : 0 ≤ (3/4 : ℝ) * (1) * (-a^2*b - a^2*c + a*b^2 + a*c^2)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * c) / (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 2 / (a + b + c) ≥ (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
