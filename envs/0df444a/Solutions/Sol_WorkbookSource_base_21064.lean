-- Prove2me | solution 1 for WorkbookSource.base_21064
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:44:19.877884+00:00
-- url     : https://prove2.me/submissions/45f94c52-0064-4a51-927e-ad43030711c5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a + 2 * (a * b + b * c + c * a) ≥ 24  := by
  have hhom : 0 ≤ (a^4*c/6 - 2*a^3*b*c/3 + a^3*c^2/6 + a^2*b^3/6 + a^2*b^2*c/3 + a^2*b*c^2/3 + a*b^4/6 - 2*a*b^3*c/3 + a*b^2*c^2/3 - 2*a*b*c^3/3 + b^2*c^3/6 + b*c^4/6) := by
    have hs0 : 0 ≤ (2/3 : ℝ) * (c) * (-a^2/2 + a*b - b*c/2)^2 := by positivity
    have hs1 : 0 ≤ (2/3 : ℝ) * (b) * (-a*b/2 + a*c - c^2/2)^2 := by positivity
    have hs2 : 0 ≤ (2/3 : ℝ) * (a) * (-a*c/2 - b^2/2 + b*c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hehom : (a^3*c + 2*a^2*b^2*c + 2*a^2*b*c^2 - a^2*b*c + a*b^3 + 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 - 24*a*b*c + b*c^3) = (a^4*c/6 - 2*a^3*b*c/3 + a^3*c^2/6 + a^2*b^3/6 + a^2*b^2*c/3 + a^2*b*c^2/3 + a*b^4/6 - 2*a*b^3*c/3 + a*b^2*c^2/3 - 2*a*b*c^3/3 + b^2*c^3/6 + b*c^4/6) := by
    linear_combination (-a^3*c/6 + 5*a^2*b*c/6 - a*b^3/6 + 5*a*b^2*c/6 + 5*a*b*c^2/6 + 4*a*b*c - b*c^3/6) * habc
  have hn : 0 ≤ (a^3*c + 2*a^2*b^2*c + 2*a^2*b*c^2 - a^2*b*c + a*b^3 + 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 - 24*a*b*c + b*c^3) := by linarith only [hhom, hehom]
  have hd : 0 < (a*b*c) := by positivity
  have heqrat : ( (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a + 2 * (a * b + b * c + c * a) ) - ( 24  ) = (a^3*c + 2*a^2*b^2*c + 2*a^2*b*c^2 - a^2*b*c + a*b^3 + 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 - 24*a*b*c + b*c^3) / (a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6), (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a + 2 * (a * b + b * c + c * a) ≥ 24) := @solution
#print axioms solution
