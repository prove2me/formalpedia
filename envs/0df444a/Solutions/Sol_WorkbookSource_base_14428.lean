-- Prove2me | solution 1 for WorkbookSource.base_14428
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:33.91083+00:00
-- url     : https://prove2.me/submissions/eb368886-902c-4e80-af98-a151e74ea70a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4  := by
  have hn : 0 ≤ (a^4*c + a^3*b^2 - 4*a^3*b*c + 2*a^2*b^2*c + 2*a^2*b*c^2 + a^2*c^3 + a*b^4 - 4*a*b^3*c + 2*a*b^2*c^2 - 4*a*b*c^3 + b^3*c^2 + b*c^4) := by
    have hs0 : 0 ≤ (1 : ℝ) * (c) * (a^2/2 - a*b/2 - a*c + b*c)^2 := by positivity
    have hs1 : 0 ≤ (3/4 : ℝ) * (c) * (-a^2 + a*b)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b) * (a*b/2 - a*c - b*c/2 + c^2)^2 := by positivity
    have hs3 : 0 ≤ (3/4 : ℝ) * (b) * (-a*b + b*c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (a) * (a*b/2 - a*c/2 - b^2 + b*c)^2 := by positivity
    have hs5 : 0 ≤ (3/4 : ℝ) * (a) * (-a*b + a*c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / b + b / c + c / a + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4) := @solution
#print axioms solution
