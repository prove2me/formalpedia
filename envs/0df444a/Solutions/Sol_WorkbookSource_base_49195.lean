-- Prove2me | solution 1 for WorkbookSource.base_49195
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:24.291505+00:00
-- url     : https://prove2.me/submissions/1ec13f71-41b8-4da2-8980-32d165955b11

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c) * (a + b + c - 1) ^ 2 + 12 ≥ 8 * (a + b + c)  := by
  have hn : 0 ≤ (a^3*b + a^3*c + 2*a^2*b^2 - 3*a^2*b*c - 2*a^2*b + 2*a^2*c^2 - 2*a^2*c + a*b^3 - 3*a*b^2*c - 2*a*b^2 - 3*a*b*c^2 + 6*a*b*c + a*b + a*c^3 - 2*a*c^2 + a*c + b^3*c + 2*b^2*c^2 - 2*b^2*c + b*c^3 - 2*b*c^2 + b*c) := by
    have hs0 : 0 ≤ (1 : ℝ) * (b*c) * (a - b - c + 1)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (a*c) * (-a + b - c + 1)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a*b) * (-a - b + c + 1)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < (a*b*c) := by positivity
  have heqrat : ( (1 / a + 1 / b + 1 / c) * (a + b + c - 1) ^ 2 + 12 ) - ( 8 * (a + b + c)  ) = (a^3*b + a^3*c + 2*a^2*b^2 - 3*a^2*b*c - 2*a^2*b + 2*a^2*c^2 - 2*a^2*c + a*b^3 - 3*a*b^2*c - 2*a*b^2 - 3*a*b*c^2 + 6*a*b*c + a*b + a*c^3 - 2*a*c^2 + a*c + b^3*c + 2*b^2*c^2 - 2*b^2*c + b*c^3 - 2*b*c^2 + b*c) / (a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (1 / a + 1 / b + 1 / c) * (a + b + c - 1) ^ 2 + 12 ≥ 8 * (a + b + c)) := @solution
#print axioms solution
