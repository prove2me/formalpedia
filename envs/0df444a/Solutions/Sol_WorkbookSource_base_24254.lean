-- Prove2me | solution 1 for WorkbookSource.base_24254
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:11.802089+00:00
-- url     : https://prove2.me/submissions/356eb6cc-525d-4e19-8028-2cb6e14b6b07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 3 / y / z + (z + x) ^ 3 / z / x + (x + y) ^ 3 / x / y ≥ 16 * (x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y^2 + 2*x^5*y*z + x^5*z^2 + x^4*y^3 - 7*x^4*y^2*z - 7*x^4*y*z^2 + x^4*z^3 + x^3*y^4 - 2*x^3*y^3*z + 10*x^3*y^2*z^2 - 2*x^3*y*z^3 + x^3*z^4 + x^2*y^5 - 7*x^2*y^4*z + 10*x^2*y^3*z^2 + 10*x^2*y^2*z^3 - 7*x^2*y*z^4 + x^2*z^5 + 2*x*y^5*z - 7*x*y^4*z^2 - 2*x*y^3*z^3 - 7*x*y^2*z^4 + 2*x*y*z^5 + y^5*z^2 + y^4*z^3 + y^3*z^4 + y^2*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^3 * (y - x)^4 + (16 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (24 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (16 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (8 : ℝ) * x^3 * (z - y)^4 + (20 : ℝ) * x^2 * (y - x)^5 + (50 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (68 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (52 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (22 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (4 : ℝ) * x^2 * (z - y)^5 + (16 : ℝ) * x^1 * (y - x)^6 + (48 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (65 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (50 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (21 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (4 : ℝ) * (y - x)^7 + (14 : ℝ) * (y - x)^6 * (z - y)^1 + (20 : ℝ) * (y - x)^5 * (z - y)^2 + (15 : ℝ) * (y - x)^4 * (z - y)^3 + (6 : ℝ) * (y - x)^3 * (z - y)^4 + (1 : ℝ) * (y - x)^2 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y^2 + 2*x^5*y*z + x^5*z^2 + x^4*y^3 - 7*x^4*y^2*z - 7*x^4*y*z^2 + x^4*z^3 + x^3*y^4 - 2*x^3*y^3*z + 10*x^3*y^2*z^2 - 2*x^3*y*z^3 + x^3*z^4 + x^2*y^5 - 7*x^2*y^4*z + 10*x^2*y^3*z^2 + 10*x^2*y^2*z^3 - 7*x^2*y*z^4 + x^2*z^5 + 2*x*y^5*z - 7*x*y^4*z^2 - 2*x*y^3*z^3 - 7*x*y^2*z^4 + 2*x*y*z^5 + y^5*z^2 + y^4*z^3 + y^3*z^4 + y^2*z^5) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ ((x^2*y + x^2*z + x*y^2 - 6*x*y*z + x*z^2 + y^2*z + y*z^2)*(x^3*y + x^3*z - 2*x^2*y*z + x*y^3 - 2*x*y^2*z - 2*x*y*z^2 + x*z^3 + y^3*z + y*z^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) ^ 3 / y / z + (z + x) ^ 3 / z / x + (x + y) ^ 3 / x / y ≥ 16 * (x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x))) := @solution
#print axioms solution
