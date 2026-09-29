-- Prove2me | solution 1 for WorkbookSource.base_1603
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:53.689146+00:00
-- url     : https://prove2.me/submissions/1be9699e-3dff-403f-b420-026464840bc5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / 3 ≥ 3 / (1 / a + 1 / b + 1 / c) + (a - b) ^ 2 / (3 * (a + b + c))  := by
  have hn : 0 ≤ (4*a^2*b^2 - 3*a^2*b*c + 2*a^2*c^2 - 3*a*b^2*c - 4*a*b*c^2 + a*c^3 + 2*b^2*c^2 + b*c^3) := by
    have hs0 : 0 ≤ (4 : ℝ) * (1) * (a*b - a*c/2 - b*c/2)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (1) * (-a*c + b*c)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b*c) * (-a + c)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*c) * (-b + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : 0 < (3*(a + b + c)*(a*b + a*c + b*c) : ℝ) := by positivity
  have he : ( (a + b + c) / 3 ) - ( 3 / (1 / a + 1 / b + 1 / c) + (a - b) ^ 2 / (3 * (a + b + c))  ) = (4*a^2*b^2 - 3*a^2*b*c + 2*a^2*c^2 - 3*a*b^2*c - 4*a*b*c^2 + a*c^3 + 2*b^2*c^2 + b*c^3) / (3*(a + b + c)*(a*b + a*c + b*c)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  rw [← he] at hp
  linarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) / 3 ≥ 3 / (1 / a + 1 / b + 1 / c) + (a - b) ^ 2 / (3 * (a + b + c))) := @solution
#print axioms solution
