-- Prove2me | solution 1 for WorkbookSource.base_4242
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:39.750875+00:00
-- url     : https://prove2.me/submissions/72d1857f-ab81-467a-b1ee-1ff404e1a051

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 24  := by
  have hhom : 0 ≤ (a^5*c/36 - a^4*b*c/18 + a^4*c^2/18 + a^3*b^3/36 - 11*a^3*b^2*c/36 - 5*a^3*b*c^2/18 + a^3*c^3/36 + a^2*b^4/18 - 5*a^2*b^3*c/18 + 7*a^2*b^2*c^2/3 - 11*a^2*b*c^3/36 + a*b^5/36 - a*b^4*c/18 - 11*a*b^3*c^2/36 - 5*a*b^2*c^3/18 - a*b*c^4/18 + b^3*c^3/36 + b^2*c^4/18 + b*c^5/36) := by
    have hs0 : 0 ≤ (4/9 : ℝ) * (b*c) * (-a^2/2 + a*b + 3*a*c/4 - b*c/4 - c^2/4)^2 := by positivity
    have hs1 : 0 ≤ (4/9 : ℝ) * (a*c) * (-a^2/4 + 3*a*b/4 - a*c/4 - b^2/2 + b*c)^2 := by positivity
    have hs2 : 0 ≤ (4/9 : ℝ) * (a*b) * (-a*b/4 + a*c - b^2/4 + 3*b*c/4 - c^2/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hehom : (a^3*c + 3*a^2*b^2*c^2 + a*b^3 - 24*a*b*c + b*c^3) = (a^5*c/36 - a^4*b*c/18 + a^4*c^2/18 + a^3*b^3/36 - 11*a^3*b^2*c/36 - 5*a^3*b*c^2/18 + a^3*c^3/36 + a^2*b^4/18 - 5*a^2*b^3*c/18 + 7*a^2*b^2*c^2/3 - 11*a^2*b*c^3/36 + a*b^5/36 - a*b^4*c/18 - 11*a*b^3*c^2/36 - 5*a*b^2*c^3/18 - a*b*c^4/18 + b^3*c^3/36 + b^2*c^4/18 + b*c^5/36) := by
    linear_combination (-a^4*c/36 + a^3*b*c/12 - a^3*c^2/36 - a^3*c/6 - a^2*b^3/36 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 + 2*a^2*b*c/3 - a*b^4/36 + a*b^3*c/12 - a*b^3/6 + 2*a*b^2*c^2/9 + 2*a*b^2*c/3 + a*b*c^3/12 + 2*a*b*c^2/3 + 4*a*b*c - b^2*c^3/36 - b*c^4/36 - b*c^3/6) * habc
  have hn : 0 ≤ (a^3*c + 3*a^2*b^2*c^2 + a*b^3 - 24*a*b*c + b*c^3) := by linarith only [hhom, hehom]
  have hd : 0 < (a*b*c) := by positivity
  have heqrat : ( a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ) - ( 24  ) = (a^3*c + 3*a^2*b^2*c^2 + a*b^3 - 24*a*b*c + b*c^3) / (a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6), a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 24) := @solution
#print axioms solution
