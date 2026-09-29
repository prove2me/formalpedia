-- Prove2me | solution 1 for WorkbookSource.base_12883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:02.90256+00:00
-- url     : https://prove2.me/submissions/dedc1413-0e90-4080-958c-ab94de44f589

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (y + z - x ^ 2) / (y + z + 4 * x) + (z + x - y ^ 2) / (z + x + 4 * y) + (x + y - z ^ 2) / (x + y + 4 * z) ≥ 1 / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^4 + 5*x^3*y + 5*x^3*z + 6*x^2*y^2 - 18*x^2*y*z + 6*x^2*z^2 + 5*x*y^3 - 18*x*y^2*z - 18*x*y*z^2 + 5*x*z^3 + 2*y^4 + 5*y^3*z + 6*y^2*z^2 + 5*y*z^3 + 2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * x^2 * (y - x)^2 + (36 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (36 : ℝ) * x^2 * (z - y)^2 + (54 : ℝ) * x^1 * (y - x)^3 + (81 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (63 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (18 : ℝ) * x^1 * (z - y)^3 + (20 : ℝ) * (y - x)^4 + (40 : ℝ) * (y - x)^3 * (z - y)^1 + (33 : ℝ) * (y - x)^2 * (z - y)^2 + (13 : ℝ) * (y - x)^1 * (z - y)^3 + (2 : ℝ) * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^4 + 5*x^3*y + 5*x^3*z + 6*x^2*y^2 - 18*x^2*y*z + 6*x^2*z^2 + 5*x*y^3 - 18*x*y^2*z - 18*x*y*z^2 + 5*x*z^3 + 2*y^4 + 5*y^3*z + 6*y^2*z^2 + 5*y*z^3 + 2*z^4) := by
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
  have he : (-2*x^4 - 10*x^3*y - 10*x^3*z + 12*x^3 - 16*x^2*y^2 - 34*x^2*y*z + 33*x^2*y - 16*x^2*z^2 + 33*x^2*z - 10*x*y^3 - 34*x*y^2*z + 33*x*y^2 - 34*x*y*z^2 - 18*x*y*z - 10*x*z^3 + 33*x*z^2 - 2*y^4 - 10*y^3*z + 12*y^3 - 16*y^2*z^2 + 33*y^2*z - 10*y*z^3 + 33*y*z^2 - 2*z^4 + 12*z^3) = (2*x^4 + 5*x^3*y + 5*x^3*z + 6*x^2*y^2 - 18*x^2*y*z + 6*x^2*z^2 + 5*x*y^3 - 18*x*y^2*z - 18*x*y*z^2 + 5*x*z^3 + 2*y^4 + 5*y^3*z + 6*y^2*z^2 + 5*y*z^3 + 2*z^4) := by
    linear_combination (-4*x^3 - 11*x^2*y - 11*x^2*z - 11*x*y^2 + 6*x*y*z - 11*x*z^2 - 4*y^3 - 11*y^2*z - 11*y*z^2 - 4*z^3) * h
  have hn : 0 ≤ (-2*x^4 - 10*x^3*y - 10*x^3*z + 12*x^3 - 16*x^2*y^2 - 34*x^2*y*z + 33*x^2*y - 16*x^2*z^2 + 33*x^2*z - 10*x*y^3 - 34*x*y^2*z + 33*x*y^2 - 34*x*y*z^2 - 18*x*y*z - 10*x*z^3 + 33*x*z^2 - 2*y^4 - 10*y^3*z + 12*y^3 - 16*y^2*z^2 + 33*y^2*z - 10*y*z^3 + 33*y*z^2 - 2*z^4 + 12*z^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (y + z - x ^ 2) / (y + z + 4 * x) + (z + x - y ^ 2) / (z + x + 4 * y) + (x + y - z ^ 2) / (x + y + 4 * z) ≥ 1 / 2) := @solution
#print axioms solution
