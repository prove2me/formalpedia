-- Prove2me | solution 1 for WorkbookSource.base_35577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:53.868518+00:00
-- url     : https://prove2.me/submissions/679beb4b-8208-44dd-bb98-233c449257fe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2) + (2 * y ^ 2 + x * z) / (x ^ 2 + z ^ 2) + (2 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2) ≥ 9 / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^6 - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 2*x^3*y^3 + 2*x^3*y^2*z + 2*x^3*y*z^2 + 2*x^3*z^3 - 5*x^2*y^4 + 2*x^2*y^3*z - 6*x^2*y^2*z^2 + 2*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^4*z + 2*x*y^3*z^2 + 2*x*y^2*z^3 + 2*x*y*z^4 + 4*y^6 - 5*y^4*z^2 + 2*y^3*z^3 - 5*y^2*z^4 + 4*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * x^4 * (y - x)^2 + (24 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (24 : ℝ) * x^4 * (z - y)^2 + (40 : ℝ) * x^3 * (y - x)^3 + (60 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (132 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (56 : ℝ) * x^3 * (z - y)^3 + (28 : ℝ) * x^2 * (y - x)^4 + (56 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (216 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (188 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (52 : ℝ) * x^2 * (z - y)^4 + (8 : ℝ) * x^1 * (y - x)^5 + (20 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (144 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (196 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (112 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (24 : ℝ) * x^1 * (z - y)^5 + (31 : ℝ) * (y - x)^4 * (z - y)^2 + (62 : ℝ) * (y - x)^3 * (z - y)^3 + (55 : ℝ) * (y - x)^2 * (z - y)^4 + (24 : ℝ) * (y - x)^1 * (z - y)^5 + (4 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^6 - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 2*x^3*y^3 + 2*x^3*y^2*z + 2*x^3*y*z^2 + 2*x^3*z^3 - 5*x^2*y^4 + 2*x^2*y^3*z - 6*x^2*y^2*z^2 + 2*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^4*z + 2*x*y^3*z^2 + 2*x*y^2*z^3 + 2*x*y*z^4 + 4*y^6 - 5*y^4*z^2 + 2*y^3*z^3 - 5*y^2*z^4 + 4*z^6) := by
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
  have hn : 0 ≤ (4*x^6 - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 2*x^3*y^3 + 2*x^3*y^2*z + 2*x^3*y*z^2 + 2*x^3*z^3 - 5*x^2*y^4 + 2*x^2*y^3*z - 6*x^2*y^2*z^2 + 2*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^4*z + 2*x*y^3*z^2 + 2*x*y^2*z^3 + 2*x*y*z^4 + 4*y^6 - 5*y^4*z^2 + 2*y^3*z^3 - 5*y^2*z^4 + 4*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2) + (2 * y ^ 2 + x * z) / (x ^ 2 + z ^ 2) + (2 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2) ≥ 9 / 2) := @solution
#print axioms solution
