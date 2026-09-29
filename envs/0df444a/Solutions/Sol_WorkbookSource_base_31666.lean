-- Prove2me | solution 1 for WorkbookSource.base_31666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:46:57.05266+00:00
-- url     : https://prove2.me/submissions/521e60e3-c133-4af4-803d-5be563347f18

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 20 * a * b / (a + c) / (b + c) + 15 * b * c / (b + a) / (c + a) + 12 * c * a / (c + b) / (a + b) ≥ 11  := by
  have hn : 0 ≤ (9*a^2*b + a^2*c + 9*a*b^2 - 22*a*b*c + a*c^2 + 4*b^2*c + 4*b*c^2) := by
    have hs0 : 0 ≤ (4 : ℝ) * (c) * (-a/2 + b)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (b) * (a - 2*c/3)^2 := by positivity
    have hs2 : 0 ≤ (9 : ℝ) * (a) * (b - c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < ((a + b)*(a + c)*(b + c)) := by positivity
  have heqrat : ( 20 * a * b / (a + c) / (b + c) + 15 * b * c / (b + a) / (c + a) + 12 * c * a / (c + b) / (a + b) ) - ( 11  ) = (9*a^2*b + a^2*c + 9*a*b^2 - 22*a*b*c + a*c^2 + 4*b^2*c + 4*b*c^2) / ((a + b)*(a + c)*(b + c)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 20 * a * b / (a + c) / (b + c) + 15 * b * c / (b + a) / (c + a) + 12 * c * a / (c + b) / (a + b) ≥ 11) := @solution
#print axioms solution
