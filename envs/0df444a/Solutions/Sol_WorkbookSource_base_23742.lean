-- Prove2me | solution 1 for WorkbookSource.base_23742
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:31:44.649984+00:00
-- url     : https://prove2.me/submissions/e3a30f39-64c4-4aca-b05f-67ba0a11aca2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b : ℝ) : (a^2 + 1) / (b^2 + 1) + (b^2 + 1) / (a^2 + 1) + (3 * (a^2 + 1) * (b^2 + 1)) / 4 ≥ 2 + a^2 - a * b + b^2  := by
  have hsum : 0 ≤ (3 : ℝ) * (-a^2*b^2 + 1)^2 + (3 : ℝ) * (-a^2 + b^2)^2 + (2 : ℝ) * (a^2*b + a*b^2 + a + b)^2 := by positivity
  have hid : (3*a^4*b^4 + 2*a^4*b^2 + 3*a^4 + 4*a^3*b^3 + 4*a^3*b + 2*a^2*b^4 - 4*a^2*b^2 + 2*a^2 + 4*a*b^3 + 4*a*b + 3*b^4 + 2*b^2 + 3) = (3 : ℝ) * (-a^2*b^2 + 1)^2 + (3 : ℝ) * (-a^2 + b^2)^2 + (2 : ℝ) * (a^2*b + a*b^2 + a + b)^2 := by ring
  have hn : 0 ≤ (3*a^4*b^4 + 2*a^4*b^2 + 3*a^4 + 4*a^3*b^3 + 4*a^3*b + 2*a^2*b^4 - 4*a^2*b^2 + 2*a^2 + 4*a*b^3 + 4*a*b + 3*b^4 + 2*b^2 + 3) := by linarith only [hsum, hid]
  have hd : (0 : ℝ) < (4*(a^2 + 1)*(b^2 + 1)) := by positivity
  have hrat : ( (a^2 + 1) / (b^2 + 1) + (b^2 + 1) / (a^2 + 1) + (3 * (a^2 + 1) * (b^2 + 1)) / 4 ) - ( 2 + a^2 - a * b + b^2  ) = (3*a^4*b^4 + 2*a^4*b^2 + 3*a^4 + 4*a^3*b^3 + 4*a^3*b + 2*a^2*b^4 - 4*a^2*b^2 + 2*a^2 + 4*a*b^3 + 4*a*b + 3*b^4 + 2*b^2 + 3) / (4*(a^2 + 1)*(b^2 + 1)) := by
    field_simp (disch := positivity)
    <;> ring
  have hf := div_nonneg hn (le_of_lt hd)
  linarith only [hf, hrat]
example : (∀ (a b : ℝ), (a^2 + 1) / (b^2 + 1) + (b^2 + 1) / (a^2 + 1) + (3 * (a^2 + 1) * (b^2 + 1)) / 4 ≥ 2 + a^2 - a * b + b^2) := @solution
#print axioms solution
