-- Prove2me | solution 1 for WorkbookSource.plus_67249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:31:45.312011+00:00
-- url     : https://prove2.me/submissions/b2a2e1ba-383a-4841-a093-2a45d8ee833a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b : ℝ) : (a + b) * (1 - a * b) / (a ^ 2 + 1) / (b ^ 2 + 1) ≤ 1 / 2   := by
  have hsum : 0 ≤ (1 : ℝ) * (-a*b - a - b + 1)^2 := by positivity
  have hid : ((a*b + a + b - 1)^2) = (1 : ℝ) * (-a*b - a - b + 1)^2 := by ring
  have hn : 0 ≤ ((a*b + a + b - 1)^2) := by linarith only [hsum, hid]
  have hd : (0 : ℝ) < (2*(a^2 + 1)*(b^2 + 1)) := by positivity
  have hrat : ( 1 / 2   ) - ( (a + b) * (1 - a * b) / (a ^ 2 + 1) / (b ^ 2 + 1) ) = ((a*b + a + b - 1)^2) / (2*(a^2 + 1)*(b^2 + 1)) := by
    field_simp (disch := positivity)
    <;> ring
  have hf := div_nonneg hn (le_of_lt hd)
  linarith only [hf, hrat]
example : (∀ (a b : ℝ), (a + b) * (1 - a * b) / (a ^ 2 + 1) / (b ^ 2 + 1) ≤ 1 / 2) := @solution
#print axioms solution
