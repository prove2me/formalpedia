-- Prove2me | solution 1 for WorkbookSource.base_10100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:46.0647+00:00
-- url     : https://prove2.me/submissions/50920289-9ca4-46f1-92af-854ad948c936

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a + b) ^ 2 + 2 * (a + c) ^ 2 + (b + c) ^ 2) ^ 2 / (a * b * c * (a + b + c)) ≥ 176  := by
  have hn : 0 ≤ (25*a^4 + 60*a^3*b + 40*a^3*c + 76*a^2*b^2 - 108*a^2*b*c + 46*a^2*c^2 + 48*a*b^3 - 120*a*b^2*c - 124*a*b*c^2 + 24*a*c^3 + 16*b^4 + 16*b^3*c + 28*b^2*c^2 + 12*b*c^3 + 9*c^4) := by
    have hs0 : 0 ≤ (80 : ℝ) * (1) * (3*a^2/8 + a*b - a*c/4 + 3*b^2/10 - 2*b*c/5 - 13*c^2/40)^2 := by positivity
    have hs1 : 0 ≤ (55 : ℝ) * (1) * (a^2/2 + a*c - 2*b^2/5 - 4*b*c/5 + c^2/10)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * (a + b) ^ 2 + 2 * (a + c) ^ 2 + (b + c) ^ 2) ^ 2 / (a * b * c * (a + b + c)) ≥ 176) := @solution
#print axioms solution
