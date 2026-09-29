-- Prove2me | solution 1 for WorkbookSource.base_26054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:07:51.156515+00:00
-- url     : https://prove2.me/submissions/faf04d51-7a7f-4b47-b3a8-5b291aca8eca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 5 * (x / y + y / z + z / x) ^ 2 ≥ 2 * (x + y + z) * (1 / x + 1 / y + 1 / z) + 27  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (5*x^4*z^2 + 8*x^3*y^2*z - 2*x^3*y*z^2 + 5*x^2*y^4 - 2*x^2*y^3*z - 33*x^2*y^2*z^2 + 8*x^2*y*z^3 + 8*x*y^3*z^2 - 2*x*y^2*z^3 + 5*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (26 : ℝ) * x^4 * (y - x)^2 + (26 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (26 : ℝ) * x^4 * (z - y)^2 + (78 : ℝ) * x^3 * (y - x)^3 + (132 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (106 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (26 : ℝ) * x^3 * (z - y)^3 + (83 : ℝ) * x^2 * (y - x)^4 + (196 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (177 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (64 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (5 : ℝ) * x^2 * (z - y)^4 + (36 : ℝ) * x^1 * (y - x)^5 + (110 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (122 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (58 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (10 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (5 : ℝ) * (y - x)^6 + (20 : ℝ) * (y - x)^5 * (z - y)^1 + (30 : ℝ) * (y - x)^4 * (z - y)^2 + (20 : ℝ) * (y - x)^3 * (z - y)^3 + (5 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (5*x^4*z^2 + 8*x^3*y^2*z - 2*x^3*y*z^2 + 5*x^2*y^4 - 2*x^2*y^3*z - 33*x^2*y^2*z^2 + 8*x^2*y*z^3 + 8*x*y^3*z^2 - 2*x*y^2*z^3 + 5*y^2*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (26 : ℝ) * x^4 * (z - x)^2 + (26 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (26 : ℝ) * x^4 * (y - z)^2 + (78 : ℝ) * x^3 * (z - x)^3 + (102 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (76 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (26 : ℝ) * x^3 * (y - z)^3 + (83 : ℝ) * x^2 * (z - x)^4 + (136 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (87 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (34 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (5 : ℝ) * x^2 * (y - z)^4 + (36 : ℝ) * x^1 * (z - x)^5 + (70 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (42 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (8 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (5 : ℝ) * (z - x)^6 + (10 : ℝ) * (z - x)^5 * (y - z)^1 + (5 : ℝ) * (z - x)^4 * (y - z)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*x^4*z^2 + 8*x^3*y^2*z - 2*x^3*y*z^2 + 5*x^2*y^4 - 2*x^2*y^3*z - 33*x^2*y^2*z^2 + 8*x^2*y*z^3 + 8*x*y^3*z^2 - 2*x*y^2*z^3 + 5*y^2*z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (5*x^4*z^2 + 8*x^3*y^2*z - 2*x^3*y*z^2 + 5*x^2*y^4 - 2*x^2*y^3*z - 33*x^2*y^2*z^2 + 8*x^2*y*z^3 + 8*x*y^3*z^2 - 2*x*y^2*z^3 + 5*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 5 * (x / y + y / z + z / x) ^ 2 ≥ 2 * (x + y + z) * (1 / x + 1 / y + 1 / z) + 27) := @solution
#print axioms solution
