-- Prove2me | solution 1 for WorkbookSource.plus_11815
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:00:00.040409+00:00
-- url     : https://prove2.me/submissions/da052478-60b7-4895-8f62-f701f126bc85

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) ^ 2 * (c - d) ^ 2   := by
  have hn : 0 ≤ (a^4 - 2*a^2*c^2 + 4*a^2*c*d - 2*a^2*d^2 + 4*a*b*c^2 - 12*a*b*c*d + 4*a*b*d^2 + b^4 - 2*b^2*c^2 + 4*b^2*c*d - 2*b^2*d^2 + c^4 + d^4) := by
    have hs0 : 0 ≤ (1 : ℝ) * (1) * (-a^2 + 577*a*b/985 - b^2 + c^2 - 577*c*d/985 + d^2)^2 := by positivity
    have hs1 : 0 ≤ (1/970225 : ℝ) * (1) * (-a*b + c*d)^2 := by positivity
    have hs2 : 0 ≤ (2786/985 : ℝ) * (c*d) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (1154/985 : ℝ) * (c*d) * (-c + d)^2 := by positivity
    have hs4 : 0 ≤ (2786/985 : ℝ) * (a*b) * (-c + d)^2 := by positivity
    have hs5 : 0 ≤ (1154/985 : ℝ) * (a*b) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hd : (0 : ℝ) < (1) := by positivity
  have heqrat : ( a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ) - ( 2 * (a - b) ^ 2 * (c - d) ^ 2   ) = (a^4 - 2*a^2*c^2 + 4*a^2*c*d - 2*a^2*d^2 + 4*a*b*c^2 - 12*a*b*c*d + 4*a*b*d^2 + b^4 - 2*b^2*c^2 + 4*b^2*c*d - 2*b^2*d^2 + c^4 + d^4) / (1) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) ^ 2 * (c - d) ^ 2) := @solution
#print axioms solution
