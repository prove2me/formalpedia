-- Prove2me | solution 1 for WorkbookSource.base_9638
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:32.888183+00:00
-- url     : https://prove2.me/submissions/ab824465-29cd-4cee-b16a-33c8b9e10182

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (b ^ 2 + b * c + c ^ 2) + b * (a + c) / (a ^ 2 + a * c + c ^ 2) + c * (a + b) / (a ^ 2 + a * b + b ^ 2)) ≥ 2  := by
  have hn : 0 ≤ (a^5*b + a^5*c - a^4*b^2 - a^4*c^2 - a^2*b^4 - a^2*c^4 + a*b^5 + a*c^5 + b^5*c - b^4*c^2 - b^2*c^4 + b*c^5) := by
    have hs0 : 0 ≤ (1 : ℝ) * (b*c) * (-b^2/2 - b*c/2 + c^2)^2 := by positivity
    have hs1 : 0 ≤ (3/4 : ℝ) * (b*c) * (-b^2 + b*c)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a*c) * (-a^2/2 - a*c/2 + c^2)^2 := by positivity
    have hs3 : 0 ≤ (3/4 : ℝ) * (a*c) * (-a^2 + a*c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (a*b) * (-a^2/2 - a*b/2 + b^2)^2 := by positivity
    have hs5 : 0 ≤ (3/4 : ℝ) * (a*b) * (-a^2 + a*b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (b + c) / (b ^ 2 + b * c + c ^ 2) + b * (a + c) / (a ^ 2 + a * c + c ^ 2) + c * (a + b) / (a ^ 2 + a * b + b ^ 2)) ≥ 2) := @solution
#print axioms solution
