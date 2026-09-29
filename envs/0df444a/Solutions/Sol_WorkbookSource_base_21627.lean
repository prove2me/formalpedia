-- Prove2me | solution 1 for WorkbookSource.base_21627
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:50:59.048332+00:00
-- url     : https://prove2.me/submissions/e5bae526-c694-43de-ba06-565be3da02e3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x + 1) / (x ^ 2 + 2 * x) + (y + 1) / (y ^ 2 + 2 * y) + (z + 1) / (z ^ 2 + 2 * z) ≥ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (10*x^5*y/81 + 10*x^5*z/81 + 49*x^4*y^2/81 + 8*x^4*y*z/27 + 49*x^4*z^2/81 + 26*x^3*y^3/27 - 41*x^3*y^2*z/81 - 41*x^3*y*z^2/81 + 26*x^3*z^3/27 + 49*x^2*y^4/81 - 41*x^2*y^3*z/81 - 46*x^2*y^2*z^2/9 - 41*x^2*y*z^3/81 + 49*x^2*z^4/81 + 10*x*y^5/81 + 8*x*y^4*z/27 - 41*x*y^3*z^2/81 - 41*x*y^2*z^3/81 + 8*x*y*z^4/27 + 10*x*z^5/81 + 10*y^5*z/81 + 49*y^4*z^2/81 + 26*y^3*z^3/27 + 49*y^2*z^4/81 + 10*y*z^5/81) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (28/3 : ℝ) * x^4 * (y - x)^2 + (28/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (28/3 : ℝ) * x^4 * (z - y)^2 + (754/27 : ℝ) * x^3 * (y - x)^3 + (377/9 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (295/9 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (254/27 : ℝ) * x^3 * (z - y)^3 + (824/27 : ℝ) * x^2 * (y - x)^4 + (1648/27 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (451/9 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (529/27 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (74/27 : ℝ) * x^2 * (z - y)^4 + (1162/81 : ℝ) * x^1 * (y - x)^5 + (2905/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (2788/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (1277/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (272/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (20/81 : ℝ) * x^1 * (z - y)^5 + (196/81 : ℝ) * (y - x)^6 + (196/27 : ℝ) * (y - x)^5 * (z - y)^1 + (677/81 : ℝ) * (y - x)^4 * (z - y)^2 + (374/81 : ℝ) * (y - x)^3 * (z - y)^3 + (11/9 : ℝ) * (y - x)^2 * (z - y)^4 + (10/81 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*x^5*y/81 + 10*x^5*z/81 + 49*x^4*y^2/81 + 8*x^4*y*z/27 + 49*x^4*z^2/81 + 26*x^3*y^3/27 - 41*x^3*y^2*z/81 - 41*x^3*y*z^2/81 + 26*x^3*z^3/27 + 49*x^2*y^4/81 - 41*x^2*y^3*z/81 - 46*x^2*y^2*z^2/9 - 41*x^2*y*z^3/81 + 49*x^2*z^4/81 + 10*x*y^5/81 + 8*x*y^4*z/27 - 41*x*y^3*z^2/81 - 41*x*y^2*z^3/81 + 8*x*y*z^4/27 + 10*x*z^5/81 + 10*y^5*z/81 + 49*y^4*z^2/81 + 26*y^3*z^3/27 + 49*y^2*z^4/81 + 10*y*z^5/81) := by
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
  have he : (-2*x^2*y^2*z^2 - 3*x^2*y^2*z + x^2*y^2 - 3*x^2*y*z^2 - 4*x^2*y*z + 2*x^2*y + x^2*z^2 + 2*x^2*z - 3*x*y^2*z^2 - 4*x*y^2*z + 2*x*y^2 - 4*x*y*z^2 - 4*x*y*z + 4*x*y + 2*x*z^2 + 4*x*z + y^2*z^2 + 2*y^2*z + 2*y*z^2 + 4*y*z) = (10*x^5*y/81 + 10*x^5*z/81 + 49*x^4*y^2/81 + 8*x^4*y*z/27 + 49*x^4*z^2/81 + 26*x^3*y^3/27 - 41*x^3*y^2*z/81 - 41*x^3*y*z^2/81 + 26*x^3*z^3/27 + 49*x^2*y^4/81 - 41*x^2*y^3*z/81 - 46*x^2*y^2*z^2/9 - 41*x^2*y*z^3/81 + 49*x^2*z^4/81 + 10*x*y^5/81 + 8*x*y^4*z/27 - 41*x*y^3*z^2/81 - 41*x*y^2*z^3/81 + 8*x*y*z^4/27 + 10*x*z^5/81 + 10*y^5*z/81 + 49*y^4*z^2/81 + 26*y^3*z^3/27 + 49*y^2*z^4/81 + 10*y*z^5/81) := by
    linear_combination (-10*x^4*y/81 - 10*x^4*z/81 - 13*x^3*y^2/27 - 4*x^3*y*z/81 - 10*x^3*y/27 - 13*x^3*z^2/27 - 10*x^3*z/27 - 13*x^2*y^3/27 + 28*x^2*y^2*z/27 - 29*x^2*y^2/27 + 28*x^2*y*z^2/27 + 16*x^2*y*z/27 - 10*x^2*y/9 - 13*x^2*z^3/27 - 29*x^2*z^2/27 - 10*x^2*z/9 - 10*x*y^4/81 - 4*x*y^3*z/81 - 10*x*y^3/27 + 28*x*y^2*z^2/27 + 16*x*y^2*z/27 - 10*x*y^2/9 - 4*x*y*z^3/81 + 16*x*y*z^2/27 - 4*x*y/3 - 10*x*z^4/81 - 10*x*z^3/27 - 10*x*z^2/9 - 4*x*z/3 - 10*y^4*z/81 - 13*y^3*z^2/27 - 10*y^3*z/27 - 13*y^2*z^3/27 - 29*y^2*z^2/27 - 10*y^2*z/9 - 10*y*z^4/81 - 10*y*z^3/27 - 10*y*z^2/9 - 4*y*z/3) * h
  have hn : 0 ≤ (-2*x^2*y^2*z^2 - 3*x^2*y^2*z + x^2*y^2 - 3*x^2*y*z^2 - 4*x^2*y*z + 2*x^2*y + x^2*z^2 + 2*x^2*z - 3*x*y^2*z^2 - 4*x*y^2*z + 2*x*y^2 - 4*x*y*z^2 - 4*x*y*z + 4*x*y + 2*x*z^2 + 4*x*z + y^2*z^2 + 2*y^2*z + 2*y*z^2 + 4*y*z) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (x + 1) / (x ^ 2 + 2 * x) + (y + 1) / (y ^ 2 + 2 * y) + (z + 1) / (z ^ 2 + 2 * z) ≥ 2) := @solution
#print axioms solution
