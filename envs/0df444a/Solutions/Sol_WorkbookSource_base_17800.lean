-- Prove2me | solution 1 for WorkbookSource.base_17800
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:32.219731+00:00
-- url     : https://prove2.me/submissions/2dca4554-25af-4fb7-b78d-5a674c62d945

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b^2 + c^2)/(a + b + c) + (b^2 + c^2 + d^2)/(b + c + d) + (c^2 + d^2 + a^2)/(c + d + a) + (d^2 + a^2 + b^2)/(d + a + b) ≥ a + b + c + d  := by
  have hn : 0 ≤ (2*a^4*b + 2*a^4*c + 2*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 2*a^3*b*d + 2*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b^2*d - 2*a^2*b*c^2 - 12*a^2*b*c*d - 2*a^2*b*d^2 + 2*a^2*c^3 - 2*a^2*c^2*d - 2*a^2*c*d^2 + 2*a^2*d^3 + 2*a*b^4 + 2*a*b^3*c + 2*a*b^3*d - 2*a*b^2*c^2 - 12*a*b^2*c*d - 2*a*b^2*d^2 + 2*a*b*c^3 - 12*a*b*c^2*d - 12*a*b*c*d^2 + 2*a*b*d^3 + 2*a*c^4 + 2*a*c^3*d - 2*a*c^2*d^2 + 2*a*c*d^3 + 2*a*d^4 + 2*b^4*c + 2*b^4*d + 2*b^3*c^2 + 2*b^3*c*d + 2*b^3*d^2 + 2*b^2*c^3 - 2*b^2*c^2*d - 2*b^2*c*d^2 + 2*b^2*d^3 + 2*b*c^4 + 2*b*c^3*d - 2*b*c^2*d^2 + 2*b*c*d^3 + 2*b*d^4 + 2*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 2*c*d^4) := by
    have hs0 : 0 ≤ (2 : ℝ) * (d) * (-a^2/2 - 577*a*b/985 + 577*a*c/1970 - 204*a*d/985 - b^2/2 + 577*b*c/1970 - 204*b*d/985 + c^2 + 408*c*d/985)^2 := by positivity
    have hs1 : 0 ≤ (3/2 : ℝ) * (d) * (-a^2 - 577*a*c/985 - 408*a*d/985 + b^2 + 577*b*c/985 + 408*b*d/985)^2 := by positivity
    have hs2 : 0 ≤ (2/970225 : ℝ) * (d) * (a*b - a*c/2 - a*d/2 - b*c/2 - b*d/2 + c*d)^2 := by positivity
    have hs3 : 0 ≤ (3/1940450 : ℝ) * (d) * (a*c - a*d - b*c + b*d)^2 := by positivity
    have hs4 : 0 ≤ (2 : ℝ) * (c) * (-a^2/2 - 577*a*b/985 - 204*a*c/985 + 577*a*d/1970 - b^2/2 - 204*b*c/985 + 577*b*d/1970 + 408*c*d/985 + d^2)^2 := by positivity
    have hs5 : 0 ≤ (3/2 : ℝ) * (c) * (-a^2 - 408*a*c/985 - 577*a*d/985 + b^2 + 408*b*c/985 + 577*b*d/985)^2 := by positivity
    have hs6 : 0 ≤ (2/970225 : ℝ) * (c) * (a*b - a*c/2 - a*d/2 - b*c/2 - b*d/2 + c*d)^2 := by positivity
    have hs7 : 0 ≤ (3/1940450 : ℝ) * (c) * (a*c - a*d - b*c + b*d)^2 := by positivity
    have hs8 : 0 ≤ (2 : ℝ) * (b) * (-a^2/2 - 204*a*b/985 - 577*a*c/985 + 577*a*d/1970 - 204*b*c/985 + 408*b*d/985 - c^2/2 + 577*c*d/1970 + d^2)^2 := by positivity
    have hs9 : 0 ≤ (3/2 : ℝ) * (b) * (-a^2 - 408*a*b/985 - 577*a*d/985 + 408*b*c/985 + c^2 + 577*c*d/985)^2 := by positivity
    have hs10 : 0 ≤ (2/970225 : ℝ) * (b) * (a*b - a*c/2 - a*d/2 - b*c/2 - b*d/2 + c*d)^2 := by positivity
    have hs11 : 0 ≤ (3/1940450 : ℝ) * (b) * (a*c - a*d - b*c + b*d)^2 := by positivity
    have hs12 : 0 ≤ (2 : ℝ) * (a) * (-204*a*b/985 - 204*a*c/985 + 408*a*d/985 - b^2/2 - 577*b*c/985 + 577*b*d/1970 - c^2/2 + 577*c*d/1970 + d^2)^2 := by positivity
    have hs13 : 0 ≤ (3/2 : ℝ) * (a) * (-408*a*b/985 + 408*a*c/985 - b^2 - 577*b*d/985 + c^2 + 577*c*d/985)^2 := by positivity
    have hs14 : 0 ≤ (2/970225 : ℝ) * (a) * (a*b - a*c/2 - a*d/2 - b*c/2 - b*d/2 + c*d)^2 := by positivity
    have hs15 : 0 ≤ (3/1940450 : ℝ) * (a) * (a*c - a*d - b*c + b*d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  have hd : (0 : ℝ) < ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by positivity
  have heqrat : ( (a^2 + b^2 + c^2)/(a + b + c) + (b^2 + c^2 + d^2)/(b + c + d) + (c^2 + d^2 + a^2)/(c + d + a) + (d^2 + a^2 + b^2)/(d + a + b) ) - ( a + b + c + d  ) = (2*a^4*b + 2*a^4*c + 2*a^4*d + 2*a^3*b^2 + 2*a^3*b*c + 2*a^3*b*d + 2*a^3*c^2 + 2*a^3*c*d + 2*a^3*d^2 + 2*a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b^2*d - 2*a^2*b*c^2 - 12*a^2*b*c*d - 2*a^2*b*d^2 + 2*a^2*c^3 - 2*a^2*c^2*d - 2*a^2*c*d^2 + 2*a^2*d^3 + 2*a*b^4 + 2*a*b^3*c + 2*a*b^3*d - 2*a*b^2*c^2 - 12*a*b^2*c*d - 2*a*b^2*d^2 + 2*a*b*c^3 - 12*a*b*c^2*d - 12*a*b*c*d^2 + 2*a*b*d^3 + 2*a*c^4 + 2*a*c^3*d - 2*a*c^2*d^2 + 2*a*c*d^3 + 2*a*d^4 + 2*b^4*c + 2*b^4*d + 2*b^3*c^2 + 2*b^3*c*d + 2*b^3*d^2 + 2*b^2*c^3 - 2*b^2*c^2*d - 2*b^2*c*d^2 + 2*b^2*d^3 + 2*b*c^4 + 2*b*c^3*d - 2*b*c^2*d^2 + 2*b*c*d^3 + 2*b*d^4 + 2*c^4*d + 2*c^3*d^2 + 2*c^2*d^3 + 2*c*d^4) / ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^2 + b^2 + c^2)/(a + b + c) + (b^2 + c^2 + d^2)/(b + c + d) + (c^2 + d^2 + a^2)/(c + d + a) + (d^2 + a^2 + b^2)/(d + a + b) ≥ a + b + c + d) := @solution
#print axioms solution
