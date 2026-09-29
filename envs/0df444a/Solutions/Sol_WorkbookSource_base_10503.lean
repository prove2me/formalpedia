-- Prove2me | solution 1 for WorkbookSource.base_10503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:37.639645+00:00
-- url     : https://prove2.me/submissions/6260341b-1ffc-4fe5-8300-3b1f58d5c95f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ≥ (x * y + z * x + y * z) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  := by
  have haux (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y*z - x^3*y^2*z - x^3*y*z^2 - x^2*y^3*z + 3*x^2*y^2*z^2 - x^2*y*z^3 + x*y^4*z - x*y^3*z^2 - x*y^2*z^3 + x*y*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * x^4 * (y - x)^2 + (1 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (1 : ℝ) * x^4 * (z - y)^2 + (2 : ℝ) * x^3 * (y - x)^3 + (3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (5 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (2 : ℝ) * x^3 * (z - y)^3 + (1 : ℝ) * x^2 * (y - x)^4 + (2 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (6 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (5 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^2 * (z - y)^4 + (2 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (3 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (1 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y*z - x^3*y^2*z - x^3*y*z^2 - x^2*y^3*z + 3*x^2*y^2*z^2 - x^2*y*z^3 + x*y^4*z - x*y^3*z^2 - x*y^2*z^3 + x*y*z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ≥ (x * y + z * x + y * z) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)) := @solution
#print axioms solution
