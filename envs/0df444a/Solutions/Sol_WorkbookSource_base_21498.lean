-- Prove2me | solution 1 for WorkbookSource.base_21498
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:14:29.932343+00:00
-- url     : https://prove2.me/submissions/7a7aaf61-464e-4ad1-9d16-d9e050cada10

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a  := by
  have hsqrt_aux : (∀ (rootvar0 rootvar1 : ℝ) (ha : 0 < rootvar0) (hb : 0 < rootvar1), ((rootvar0^2) + (rootvar1^2)) ^ 2 / 2 + ((rootvar0^2) + (rootvar1^2)) / 4 ≥ (rootvar0^2) * rootvar1 + (rootvar1^2) * rootvar0) := by
    intro rootvar0 rootvar1 ha hb
    have hn : 0 ≤ (2*rootvar0^4 + 4*rootvar0^2*rootvar1^2 - 4*rootvar0^2*rootvar1 + rootvar0^2 - 4*rootvar0*rootvar1^2 + 2*rootvar1^4 + rootvar1^2) := by
      have hs0 : 0 ≤ (2 : ℝ) * (1) * (3*rootvar0^2/8 - rootvar0*rootvar1/8 - 5*rootvar0/8 + rootvar1^2)^2 := by positivity
      have hs1 : 0 ≤ (55/32 : ℝ) * (1) * (rootvar0^2 - rootvar0*rootvar1/11 + 3*rootvar0/11 - 8*rootvar1/11)^2 := by positivity
      have hs2 : 0 ≤ (16/11 : ℝ) * (1) * (rootvar0*rootvar1 - rootvar0/4 - rootvar1/4)^2 := by positivity
      have hs3 : 0 ≤ (1/2 : ℝ) * (rootvar0*rootvar1) * (-rootvar0 - rootvar1 + 1)^2 := by positivity
      nlinarith only [hs0, hs1, hs2, hs3]
    have hd : (0 : ℝ) < (4) := by positivity
    have heqrat : (  ((rootvar0^2) + (rootvar1^2)) ^ 2 / 2 + ((rootvar0^2) + (rootvar1^2)) / 4 ) - ( (rootvar0^2) * rootvar1 + (rootvar1^2) * rootvar0   ) = (2*rootvar0^4 + 4*rootvar0^2*rootvar1^2 - 4*rootvar0^2*rootvar1 + rootvar0^2 - 4*rootvar0*rootvar1^2 + 2*rootvar1^4 + rootvar1^2) / (4) := by
      field_simp (disch := positivity)
      <;> ring
    have hp := div_nonneg hn (le_of_lt hd)
    linarith only [heqrat, hp]
  have hsqrt_square0 : (Real.sqrt a)^2 = a := Real.sq_sqrt (by positivity)
  have hsqrt_square1 : (Real.sqrt b)^2 = b := Real.sq_sqrt (by positivity)
  simpa only [hsqrt_square0, hsqrt_square1] using (hsqrt_aux (Real.sqrt a) (Real.sqrt b) (by positivity) (by positivity))
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), (a + b) ^ 2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a) := @solution
#print axioms solution
