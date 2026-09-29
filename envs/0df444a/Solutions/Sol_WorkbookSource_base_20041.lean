-- Prove2me | solution 1 for WorkbookSource.base_20041
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:35.186423+00:00
-- url     : https://prove2.me/submissions/8981a50a-d940-430a-889f-5b7d819a478c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a : ℝ) (ha : 0 < a) : a + (1/a) + (1/(a + (1/a))) ≥ 5/2  := by
  have hn : 0 ≤ ((a - 1)^2*(2*a^2 - a + 2)) := by
    have hs0 : 0 ≤ (5 : ℝ) * (1) * (-a^2/2 + a - 1/2)^2 := by positivity
    have hs1 : 0 ≤ (3/4 : ℝ) * (1) * (1 - a^2)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : 0 < (2*a*(a^2 + 1)) := by positivity
  have heqrat : ( a + (1/a) + (1/(a + (1/a))) ) - ( 5/2  ) = ((a - 1)^2*(2*a^2 - a + 2)) / (2*a*(a^2 + 1)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a : ℝ) (ha : 0 < a), a + (1/a) + (1/(a + (1/a))) ≥ 5/2) := @solution
#print axioms solution
