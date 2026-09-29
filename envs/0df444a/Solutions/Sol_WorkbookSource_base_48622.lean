-- Prove2me | solution 1 for WorkbookSource.base_48622
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:51:29.615139+00:00
-- url     : https://prove2.me/submissions/70d9acf0-a10a-4331-b1bd-c7cae614ad06

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 23) * (a + 2 * b + c)^2  := by
  have hn : 0 ≤ (16*a^2 - 5*a*b - 14*a*c + 18*b^2 - 28*b*c + 16*c^2) := by
    have hs0 : 0 ≤ (18 : ℝ) * (1) * (-5*a/36 + b - 7*c/9)^2 := by positivity
    have hs1 : 0 ≤ (1127/72 : ℝ) * (1) * (a - 4*c/7)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : (0 : ℝ) < (23) := by positivity
  have heqrat : ( a^2 + 2 * b^2 + c^2 + a * b ) - ( (7 / 23) * (a + 2 * b + c)^2  ) = (16*a^2 - 5*a*b - 14*a*c + 18*b^2 - 28*b*c + 16*c^2) / (23) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 + 2 * b^2 + c^2 + a * b ≥ (7 / 23) * (a + 2 * b + c)^2) := @solution
#print axioms solution
