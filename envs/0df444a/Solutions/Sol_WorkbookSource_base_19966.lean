-- Prove2me | solution 1 for WorkbookSource.base_19966
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:14:29.278526+00:00
-- url     : https://prove2.me/submissions/7cf47037-eb3f-4813-a7a5-a84dfa48c644

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2) ≥ 2 / (x + y + 2)  := by
  have hsqrt_aux : (∀ (rootvar0 rootvar1 : ℝ) (hx : 0 < rootvar0) (hy : 0 < rootvar1), (1 / (1 + rootvar0) ^ 2 + 1 / (1 + rootvar1) ^ 2) ≥ 2 / ((rootvar0^2) + (rootvar1^2) + 2)) := by
    intro rootvar0 rootvar1 hx hy
    have hn : 0 ≤ (rootvar0^4 + 2*rootvar0^3 - 2*rootvar0^2*rootvar1 + 2*rootvar0^2 - 2*rootvar0*rootvar1^2 - 8*rootvar0*rootvar1 + rootvar1^4 + 2*rootvar1^3 + 2*rootvar1^2 + 2) := by
      have hs0 : 0 ≤ (2 : ℝ) * (1) * (-rootvar0*rootvar1 + 1)^2 := by positivity
      have hs1 : 0 ≤ (2 : ℝ) * (1) * (-rootvar0^2/2 - rootvar0 + rootvar1^2/2 + rootvar1)^2 := by positivity
      have hs2 : 0 ≤ (1/2 : ℝ) * (1) * (-rootvar0^2 + rootvar1^2)^2 := by positivity
      nlinarith only [hs0, hs1, hs2]
    have hd : (0 : ℝ) < ((rootvar0 + 1)^2*(rootvar1 + 1)^2*(rootvar0^2 + rootvar1^2 + 2)) := by positivity
    have heqrat : (  (1 / (1 + rootvar0) ^ 2 + 1 / (1 + rootvar1) ^ 2) ) - ( 2 / ((rootvar0^2) + (rootvar1^2) + 2)   ) = (rootvar0^4 + 2*rootvar0^3 - 2*rootvar0^2*rootvar1 + 2*rootvar0^2 - 2*rootvar0*rootvar1^2 - 8*rootvar0*rootvar1 + rootvar1^4 + 2*rootvar1^3 + 2*rootvar1^2 + 2) / ((rootvar0 + 1)^2*(rootvar1 + 1)^2*(rootvar0^2 + rootvar1^2 + 2)) := by
      field_simp (disch := positivity)
      <;> ring
    have hp := div_nonneg hn (le_of_lt hd)
    linarith only [heqrat, hp]
  have hsqrt_square0 : (Real.sqrt x)^2 = x := Real.sq_sqrt (by positivity)
  have hsqrt_square1 : (Real.sqrt y)^2 = y := Real.sq_sqrt (by positivity)
  simpa only [hsqrt_square0, hsqrt_square1] using (hsqrt_aux (Real.sqrt x) (Real.sqrt y) (by positivity) (by positivity))
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), (1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2) ≥ 2 / (x + y + 2)) := @solution
#print axioms solution
