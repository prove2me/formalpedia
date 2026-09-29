-- Prove2me | solution 1 for WorkbookSource.base_32348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:46:57.755658+00:00
-- url     : https://prove2.me/submissions/ff779f21-c93a-43a9-9473-0734a9fbfb5a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (14 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2 - 2  := by
  have hn : 0 ≤ (a^4*c + a^3*b^2 - 10*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + 7*a^2*b^2*c + 7*a^2*b*c^2 + a^2*c^3 + a*b^4 - 10*a*b^3*c + 7*a*b^2*c^2 - 10*a*b*c^3 + b^3*c^2 + 2*b^2*c^3 + b*c^4) := by
    have hs0 : 0 ≤ (9 : ℝ) * (c) * (-a^2/3 + a*b + a*c/3 - 2*b*c/3)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (b) * (-2*a*b/3 + a*c + b*c/3 - c^2/3)^2 := by positivity
    have hs2 : 0 ≤ (9 : ℝ) * (a) * (a*b/3 - 2*a*c/3 - b^2/3 + b*c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < (a*b*c*(a + b + c)^2) := by positivity
  have heqrat : ( (a / b + b / c + c / a) ) - ( (14 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2 - 2  ) = (a^4*c + a^3*b^2 - 10*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + 7*a^2*b^2*c + 7*a^2*b*c^2 + a^2*c^3 + a*b^4 - 10*a*b^3*c + 7*a*b^2*c^2 - 10*a*b*c^3 + b^3*c^2 + 2*b^2*c^3 + b*c^4) / (a*b*c*(a + b + c)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ≥ (14 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2 - 2) := @solution
#print axioms solution
