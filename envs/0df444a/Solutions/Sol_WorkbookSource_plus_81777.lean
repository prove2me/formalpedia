-- Prove2me | solution 1 for WorkbookSource.plus_81777
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:34:09.574087+00:00
-- url     : https://prove2.me/submissions/4545cfbd-b9df-49e8-89b2-54094c8542a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a^2 * b + b^2 * c + c^2 * d + d^2 * a ≤ 256 / 27   := by
  have hhom : 0 ≤ (4*a^3 - 15*a^2*b + 12*a^2*c + 12*a^2*d + 12*a*b^2 + 24*a*b*c + 24*a*b*d + 12*a*c^2 + 24*a*c*d - 15*a*d^2 + 4*b^3 - 15*b^2*c + 12*b^2*d + 12*b*c^2 + 24*b*c*d + 12*b*d^2 + 4*c^3 - 15*c^2*d + 12*c*d^2 + 4*d^3) := by
    have hs0 : 0 ≤ (92/5 : ℝ) * (d) * (8*a/23 + b + 2*c/23 - 4*d/23)^2 := by positivity
    have hs1 : 0 ≤ (1584/115 : ℝ) * (d) * (a + c/4 - d/2)^2 := by positivity
    have hs2 : 0 ≤ (92/5 : ℝ) * (c) * (a + 2*b/23 - 4*c/23 + 8*d/23)^2 := by positivity
    have hs3 : 0 ≤ (1584/115 : ℝ) * (c) * (b/4 - c/2 + d)^2 := by positivity
    have hs4 : 0 ≤ (92/5 : ℝ) * (b) * (2*a/23 - 4*b/23 + 8*c/23 + d)^2 := by positivity
    have hs5 : 0 ≤ (1584/115 : ℝ) * (b) * (a/4 - b/2 + c)^2 := by positivity
    have hs6 : 0 ≤ (92/5 : ℝ) * (a) * (-4*a/23 + 8*b/23 + c + 2*d/23)^2 := by positivity
    have hs7 : 0 ≤ (1584/115 : ℝ) * (a) * (-a/2 + b + d/4)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hehom : (-27*a^2*b - 27*a*d^2 - 27*b^2*c - 27*c^2*d + 256) = (4*a^3 - 15*a^2*b + 12*a^2*c + 12*a^2*d + 12*a*b^2 + 24*a*b*c + 24*a*b*d + 12*a*c^2 + 24*a*c*d - 15*a*d^2 + 4*b^3 - 15*b^2*c + 12*b^2*d + 12*b*c^2 + 24*b*c*d + 12*b*d^2 + 4*c^3 - 15*c^2*d + 12*c*d^2 + 4*d^3) := by
    linear_combination (-4*a^2 - 8*a*b - 8*a*c - 8*a*d - 16*a - 4*b^2 - 8*b*c - 8*b*d - 16*b - 4*c^2 - 8*c*d - 16*c - 4*d^2 - 16*d - 64) * hab
  have hn : 0 ≤ (-27*a^2*b - 27*a*d^2 - 27*b^2*c - 27*c^2*d + 256) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (27) := by positivity
  have heqrat : ( 256 / 27   ) - ( a^2 * b + b^2 * c + c^2 * d + d^2 * a ) = (-27*a^2*b - 27*a*d^2 - 27*b^2*c - 27*c^2*d + 256) / (27) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4), a^2 * b + b^2 * c + c^2 * d + d^2 * a ≤ 256 / 27) := @solution
#print axioms solution
