-- Prove2me | solution 1 for WorkbookSource.base_18235
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:59:50.695017+00:00
-- url     : https://prove2.me/submissions/5e565e19-6179-49ad-9923-601fd87bcd57

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : 1 / 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 1 ≥ a ^ 3 + b ^ 3 + c ^ 3  := by
  have hhom : 0 ≤ (a^4/8 - a^3*b/2 - a^3*c/2 + 3*a^2*b^2/4 + 3*a^2*b*c/2 + 3*a^2*c^2/4 - a*b^3/2 + 3*a*b^2*c/2 + 3*a*b*c^2/2 - a*c^3/2 + b^4/8 - b^3*c/2 + 3*b^2*c^2/4 - b*c^3/2 + c^4/8) := by
    have hs0 : 0 ≤ (1/2 : ℝ) * (1) * (-a^2/2 + a*b + a*c - b^2/2 + b*c - c^2/2)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b*c) * (a)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a*c) * (b)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*b) * (c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hehom : (a^4 - 2*a^3 + b^4 - 2*b^3 + c^4 - 2*c^3 + 2) = (a^4/8 - a^3*b/2 - a^3*c/2 + 3*a^2*b^2/4 + 3*a^2*b*c/2 + 3*a^2*c^2/4 - a*b^3/2 + 3*a*b^2*c/2 + 3*a*b*c^2/2 - a*c^3/2 + b^4/8 - b^3*c/2 + 3*b^2*c^2/4 - b*c^3/2 + c^4/8) := by
    linear_combination (7*a^3/8 - 3*a^2*b/8 - 3*a^2*c/8 - a^2/4 - 3*a*b^2/8 - 3*a*b*c/4 - a*b/2 - 3*a*c^2/8 - a*c/2 - a/2 + 7*b^3/8 - 3*b^2*c/8 - b^2/4 - 3*b*c^2/8 - b*c/2 - b/2 + 7*c^3/8 - c^2/4 - c/2 - 1) * habc
  have hn : 0 ≤ (a^4 - 2*a^3 + b^4 - 2*b^3 + c^4 - 2*c^3 + 2) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (2) := by positivity
  have heqrat : ( 1 / 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 1 ) - ( a ^ 3 + b ^ 3 + c ^ 3  ) = (a^4 - 2*a^3 + b^4 - 2*b^3 + c^4 - 2*c^3 + 2) / (2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2), 1 / 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 1 ≥ a ^ 3 + b ^ 3 + c ^ 3) := @solution
#print axioms solution
