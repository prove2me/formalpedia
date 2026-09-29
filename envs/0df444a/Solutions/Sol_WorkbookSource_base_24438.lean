-- Prove2me | solution 1 for WorkbookSource.base_24438
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:44:16.364564+00:00
-- url     : https://prove2.me/submissions/122df094-ee28-46c5-8745-236409f8bc96

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a ^ 2 + b ^ 2 + 3 * c ^ 2) + b * c / (b ^ 2 + c ^ 2 + 3 * a ^ 2) + c * a / (c ^ 2 + a ^ 2 + 3 * b ^ 2)) ≤ 3 / 5  := by
  have hn : 0 ≤ (9*a^6 - 15*a^5*b - 15*a^5*c + 39*a^4*b^2 - 5*a^4*b*c + 39*a^4*c^2 - 50*a^3*b^3 - 20*a^3*b^2*c - 20*a^3*b*c^2 - 50*a^3*c^3 + 39*a^2*b^4 - 20*a^2*b^3*c + 114*a^2*b^2*c^2 - 20*a^2*b*c^3 + 39*a^2*c^4 - 15*a*b^5 - 5*a*b^4*c - 20*a*b^3*c^2 - 20*a*b^2*c^3 - 5*a*b*c^4 - 15*a*c^5 + 9*b^6 - 15*b^5*c + 39*b^4*c^2 - 50*b^3*c^3 + 39*b^2*c^4 - 15*b*c^5 + 9*c^6) := by
    have hs0 : 0 ≤ (33 : ℝ) * (1) * (3*a^3/22 + 19*a^2*b/33 - 29*a^2*c/66 - 29*a*b^2/66 - 5*a*c^2/66 + b^3/11 - 41*b^2*c/66 + b*c^2 - 5*c^3/22)^2 := by positivity
    have hs1 : 0 ≤ (4331/132 : ℝ) * (1) * (441*a^3/4331 - 1724*a^2*b/4331 - 2851*a^2*c/4331 + 2363*a*b^2/4331 + a*c^2 + 624*b^3/4331 - 2119*b^2*c/4331 - 15*c^3/61)^2 := by positivity
    have hs2 : 0 ≤ (73028/4331 : ℝ) * (1) * (6831*a^3/36514 - 10883*a^2*b/36514 - 9839*a^2*c/18257 + a*b^2 - 9486*b^3/18257 - 5953*b^2*c/36514 + 12141*c^3/36514)^2 := by positivity
    have hs3 : 0 ≤ (280497/18257 : ℝ) * (1) * (-2505*a^3/4921 + a^2*b - 92*a^2*c/259 + 174*b^3/4921 - 167*b^2*c/259 + 9*c^3/19)^2 := by positivity
    have hs4 : 0 ≤ (1444/259 : ℝ) * (1) * (15*a^3/19 - a^2*c - 15*b^3/19 + b^2*c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : 0 < (5*(a^2 + b^2 + 3*c^2)*(a^2 + 3*b^2 + c^2)*(3*a^2 + b^2 + c^2)) := by positivity
  have heqrat : ( 3 / 5  ) - ( (a * b / (a ^ 2 + b ^ 2 + 3 * c ^ 2) + b * c / (b ^ 2 + c ^ 2 + 3 * a ^ 2) + c * a / (c ^ 2 + a ^ 2 + 3 * b ^ 2)) ) = (9*a^6 - 15*a^5*b - 15*a^5*c + 39*a^4*b^2 - 5*a^4*b*c + 39*a^4*c^2 - 50*a^3*b^3 - 20*a^3*b^2*c - 20*a^3*b*c^2 - 50*a^3*c^3 + 39*a^2*b^4 - 20*a^2*b^3*c + 114*a^2*b^2*c^2 - 20*a^2*b*c^3 + 39*a^2*c^4 - 15*a*b^5 - 5*a*b^4*c - 20*a*b^3*c^2 - 20*a*b^2*c^3 - 5*a*b*c^4 - 15*a*c^5 + 9*b^6 - 15*b^5*c + 39*b^4*c^2 - 50*b^3*c^3 + 39*b^2*c^4 - 15*b*c^5 + 9*c^6) / (5*(a^2 + b^2 + 3*c^2)*(a^2 + 3*b^2 + c^2)*(3*a^2 + b^2 + c^2)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (a ^ 2 + b ^ 2 + 3 * c ^ 2) + b * c / (b ^ 2 + c ^ 2 + 3 * a ^ 2) + c * a / (c ^ 2 + a ^ 2 + 3 * b ^ 2)) ≤ 3 / 5) := @solution
#print axioms solution
