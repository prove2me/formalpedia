-- Prove2me | solution 1 for WorkbookSource.plus_28550
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:28:36.248386+00:00
-- url     : https://prove2.me/submissions/97c0c93d-00ee-4dea-ae93-66a67d1564c1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a * b * c + a * b * d + b * c * d + a * c * d ≤ a * c + b * d + (a * d + a * b + b * c + c * d) / 2   := by
  have hhom : 0 ≤ (a^2*b/4 + a^2*c/2 + a^2*d/4 + a*b^2/4 - a*b*c - a*b*d + a*c^2/2 - a*c*d + a*d^2/4 + b^2*c/4 + b^2*d/2 + b*c^2/4 - b*c*d + b*d^2/2 + c^2*d/4 + c*d^2/4) := by
    have hs0 : 0 ≤ (1/2 : ℝ) * (d) * (-a/2 + b - c/2)^2 := by positivity
    have hs1 : 0 ≤ (1/8 : ℝ) * (d) * (-a + c)^2 := by positivity
    have hs2 : 0 ≤ (1/2 : ℝ) * (c) * (a - b/2 - d/2)^2 := by positivity
    have hs3 : 0 ≤ (1/8 : ℝ) * (c) * (-b + d)^2 := by positivity
    have hs4 : 0 ≤ (1/2 : ℝ) * (b) * (-a/2 - c/2 + d)^2 := by positivity
    have hs5 : 0 ≤ (1/8 : ℝ) * (b) * (-a + c)^2 := by positivity
    have hs6 : 0 ≤ (1/2 : ℝ) * (a) * (-b/2 + c - d/2)^2 := by positivity
    have hs7 : 0 ≤ (1/8 : ℝ) * (a) * (-b + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hehom : (-2*a*b*c - 2*a*b*d + a*b - 2*a*c*d + 2*a*c + a*d - 2*b*c*d + b*c + 2*b*d + c*d) = (a^2*b/4 + a^2*c/2 + a^2*d/4 + a*b^2/4 - a*b*c - a*b*d + a*c^2/2 - a*c*d + a*d^2/4 + b^2*c/4 + b^2*d/2 + b*c^2/4 - b*c*d + b*d^2/2 + c^2*d/4 + c*d^2/4) := by
    linear_combination (-a*b/4 - a*c/2 - a*d/4 - b*c/4 - b*d/2 - c*d/4) * hab
  have hn : 0 ≤ (-2*a*b*c - 2*a*b*d + a*b - 2*a*c*d + 2*a*c + a*d - 2*b*c*d + b*c + 2*b*d + c*d) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (2) := by positivity
  have heqrat : ( a * c + b * d + (a * d + a * b + b * c + c * d) / 2   ) - ( a * b * c + a * b * d + b * c * d + a * c * d ) = (-2*a*b*c - 2*a*b*d + a*b - 2*a*c*d + 2*a*c + a*d - 2*b*c*d + b*c + 2*b*d + c*d) / (2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4), a * b * c + a * b * d + b * c * d + a * c * d ≤ a * c + b * d + (a * d + a * b + b * c + c * d) / 2) := @solution
#print axioms solution
