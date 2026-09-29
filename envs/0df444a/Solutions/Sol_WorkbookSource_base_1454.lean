-- Prove2me | solution 1 for WorkbookSource.base_1454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:37.519105+00:00
-- url     : https://prove2.me/submissions/aad4660f-eda2-49e3-b52f-d61671dd2a22

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 / b + b^2 / c + c^2 / d + d^2 / a) ≥ a + b + c + d  := by
  have hn : 0 ≤ (a^3*c*d - a^2*b*c*d + a*b^3*d - a*b^2*c*d + a*b*c^3 - a*b*c^2*d - a*b*c*d^2 + b*c*d^3) := by
    have hs0 : 0 ≤ (1 : ℝ) * (b*c*d) * (-a + d)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (a*c*d) * (-a + b)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a*b*d) * (-b + c)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*b*c) * (-c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : 0 < (a*b*c*d) := by positivity
  have heqrat : ( (a^2 / b + b^2 / c + c^2 / d + d^2 / a) ) - ( a + b + c + d  ) = (a^3*c*d - a^2*b*c*d + a*b^3*d - a*b^2*c*d + a*b*c^3 - a*b*c^2*d - a*b*c*d^2 + b*c*d^3) / (a*b*c*d) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^2 / b + b^2 / c + c^2 / d + d^2 / a) ≥ a + b + c + d) := @solution
#print axioms solution
