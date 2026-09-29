-- Prove2me | solution 1 for WorkbookSource.base_36975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:21:21.995342+00:00
-- url     : https://prove2.me/submissions/da04c158-4388-4b13-b280-f1f9838ebd6e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x / y ^ 2 + y / z ^ 2 + z / x ^ 2) ≥ (x ^ 2 / y + y ^ 2 / z + z ^ 2 / x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*z^2/9 + x^4*y^3/9 - 7*x^4*y*z^2/9 + 2*x^4*z^3/9 + 2*x^3*y^4/9 + 2*x^3*y^3*z/9 + x^3*y^2*z^2/9 + 2*x^3*y*z^3/9 + x^3*z^4/9 + x^2*y^5/9 - 7*x^2*y^4*z/9 + x^2*y^3*z^2/9 + x^2*y^2*z^3/9 + 2*x*y^3*z^3/9 - 7*x*y^2*z^4/9 + y^4*z^3/9 + 2*y^3*z^4/9 + y^2*z^5/9) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * x^5 * (y - x)^2 + (2/3 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (2/3 : ℝ) * x^5 * (z - y)^2 + (28/9 : ℝ) * x^4 * (y - x)^3 + (14/3 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (2 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (2/9 : ℝ) * x^4 * (z - y)^3 + (53/9 : ℝ) * x^3 * (y - x)^4 + (106/9 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (59/9 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (2/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (1/9 : ℝ) * x^3 * (z - y)^4 + (50/9 : ℝ) * x^2 * (y - x)^5 + (128/9 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (110/9 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (37/9 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (7/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (1/9 : ℝ) * x^2 * (z - y)^5 + (23/9 : ℝ) * x^1 * (y - x)^6 + (74/9 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (89/9 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (50/9 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (14/9 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (2/9 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (4/9 : ℝ) * (y - x)^7 + (16/9 : ℝ) * (y - x)^6 * (z - y)^1 + (25/9 : ℝ) * (y - x)^5 * (z - y)^2 + (19/9 : ℝ) * (y - x)^4 * (z - y)^3 + (7/9 : ℝ) * (y - x)^3 * (z - y)^4 + (1/9 : ℝ) * (y - x)^2 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^5*z^2/9 + x^4*y^3/9 - 7*x^4*y*z^2/9 + 2*x^4*z^3/9 + 2*x^3*y^4/9 + 2*x^3*y^3*z/9 + x^3*y^2*z^2/9 + 2*x^3*y*z^3/9 + x^3*z^4/9 + x^2*y^5/9 - 7*x^2*y^4*z/9 + x^2*y^3*z^2/9 + x^2*y^2*z^3/9 + 2*x*y^3*z^3/9 - 7*x*y^2*z^4/9 + y^4*z^3/9 + 2*y^3*z^4/9 + y^2*z^5/9) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * x^5 * (z - x)^2 + (2/3 : ℝ) * x^5 * (z - x)^1 * (y - z)^1 + (2/3 : ℝ) * x^5 * (y - z)^2 + (28/9 : ℝ) * x^4 * (z - x)^3 + (14/3 : ℝ) * x^4 * (z - x)^2 * (y - z)^1 + (2 : ℝ) * x^4 * (z - x)^1 * (y - z)^2 + (2/9 : ℝ) * x^4 * (y - z)^3 + (53/9 : ℝ) * x^3 * (z - x)^4 + (106/9 : ℝ) * x^3 * (z - x)^3 * (y - z)^1 + (59/9 : ℝ) * x^3 * (z - x)^2 * (y - z)^2 + (2/3 : ℝ) * x^3 * (z - x)^1 * (y - z)^3 + (1/9 : ℝ) * x^3 * (y - z)^4 + (50/9 : ℝ) * x^2 * (z - x)^5 + (122/9 : ℝ) * x^2 * (z - x)^4 * (y - z)^1 + (98/9 : ℝ) * x^2 * (z - x)^3 * (y - z)^2 + (25/9 : ℝ) * x^2 * (z - x)^2 * (y - z)^3 + (1/9 : ℝ) * x^2 * (z - x)^1 * (y - z)^4 + (1/9 : ℝ) * x^2 * (y - z)^5 + (23/9 : ℝ) * x^1 * (z - x)^6 + (64/9 : ℝ) * x^1 * (z - x)^5 * (y - z)^1 + (64/9 : ℝ) * x^1 * (z - x)^4 * (y - z)^2 + (26/9 : ℝ) * x^1 * (z - x)^3 * (y - z)^3 + (1/3 : ℝ) * x^1 * (z - x)^2 * (y - z)^4 + (4/9 : ℝ) * (z - x)^7 + (4/3 : ℝ) * (z - x)^6 * (y - z)^1 + (13/9 : ℝ) * (z - x)^5 * (y - z)^2 + (2/3 : ℝ) * (z - x)^4 * (y - z)^3 + (1/9 : ℝ) * (z - x)^3 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*z^2/9 + x^4*y^3/9 - 7*x^4*y*z^2/9 + 2*x^4*z^3/9 + 2*x^3*y^4/9 + 2*x^3*y^3*z/9 + x^3*y^2*z^2/9 + 2*x^3*y*z^3/9 + x^3*z^4/9 + x^2*y^5/9 - 7*x^2*y^4*z/9 + x^2*y^3*z^2/9 + x^2*y^2*z^3/9 + 2*x*y^3*z^3/9 - 7*x*y^2*z^4/9 + y^4*z^3/9 + 2*y^3*z^4/9 + y^2*z^5/9) := by
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
  have he : (-x^4*y*z^2 + x^3*z^2 - x^2*y^4*z + x^2*y^3 - x*y^2*z^4 + y^2*z^3) = (x^5*z^2/9 + x^4*y^3/9 - 7*x^4*y*z^2/9 + 2*x^4*z^3/9 + 2*x^3*y^4/9 + 2*x^3*y^3*z/9 + x^3*y^2*z^2/9 + 2*x^3*y*z^3/9 + x^3*z^4/9 + x^2*y^5/9 - 7*x^2*y^4*z/9 + x^2*y^3*z^2/9 + x^2*y^2*z^3/9 + 2*x*y^3*z^3/9 - 7*x*y^2*z^4/9 + y^4*z^3/9 + 2*y^3*z^4/9 + y^2*z^5/9) := by
    linear_combination (-x^4*z^2/9 - x^3*y^3/9 - x^3*y*z^2/9 - x^3*z^3/9 - x^3*z^2/3 - x^2*y^4/9 - x^2*y^3*z/9 - x^2*y^3/3 - x*y^2*z^3/9 - y^3*z^3/9 - y^2*z^4/9 - y^2*z^3/3) * h
  have hn : 0 ≤ (-x^4*y*z^2 + x^3*z^2 - x^2*y^4*z + x^2*y^3 - x*y^2*z^4 + y^2*z^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (x / y ^ 2 + y / z ^ 2 + z / x ^ 2) ≥ (x ^ 2 / y + y ^ 2 / z + z ^ 2 / x)) := @solution
#print axioms solution
