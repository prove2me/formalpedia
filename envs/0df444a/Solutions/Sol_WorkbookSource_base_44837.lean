-- Prove2me | solution 1 for WorkbookSource.base_44837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:55.226284+00:00
-- url     : https://prove2.me/submissions/ba71aeed-a600-4a2e-a738-0d722a6f505a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + b) * (b + 2 * c) * (a + 3 * b + c) / (a * b * c) ≥ 128 / 3  := by
  have hn : 0 ≤ (6*a^2*b + 12*a^2*c + 21*a*b^2 - 80*a*b*c + 12*a*c^2 + 9*b^3 + 21*b^2*c + 6*b*c^2) := by
    have hs0 : 0 ≤ (27 : ℝ) * (c) * (-2*a/3 + b)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (b) * (-a/3 + b - c/3)^2 := by positivity
    have hs2 : 0 ≤ (5 : ℝ) * (b) * (-a + c)^2 := by positivity
    have hs3 : 0 ≤ (27 : ℝ) * (a) * (b - 2*c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : (0 : ℝ) < (3*a*b*c) := by positivity
  have heqrat : ( (2 * a + b) * (b + 2 * c) * (a + 3 * b + c) / (a * b * c) ) - ( 128 / 3  ) = (6*a^2*b + 12*a^2*c + 21*a*b^2 - 80*a*b*c + 12*a*c^2 + 9*b^3 + 21*b^2*c + 6*b*c^2) / (3*a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a + b) * (b + 2 * c) * (a + 3 * b + c) / (a * b * c) ≥ 128 / 3) := @solution
#print axioms solution
