-- Prove2me | solution 1 for WorkbookSource.plus_47977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:39:26.165568+00:00
-- url     : https://prove2.me/submissions/c0d62ae8-01e5-445b-8524-75ff717deab0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 3) : 7 * (x * y + y * z + z * x) ≤ 18 + 3 * (x * y * z) ^ 2   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^6/81 + 5*x^5*y/81 + 5*x^5*z/81 + 2*x^4*y^2/81 - x^4*y*z/27 + 2*x^4*z^2/81 - 2*x^3*y^3/81 - 34*x^3*y^2*z/81 - 34*x^3*y*z^2/81 - 2*x^3*z^3/81 + 2*x^2*y^4/81 - 34*x^2*y^3*z/81 + 19*x^2*y^2*z^2/9 - 34*x^2*y*z^3/81 + 2*x^2*z^4/81 + 5*x*y^5/81 - x*y^4*z/27 - 34*x*y^3*z^2/81 - 34*x*y^2*z^3/81 - x*y*z^4/27 + 5*x*z^5/81 + 2*y^6/81 + 5*y^5*z/81 + 2*y^4*z^2/81 - 2*y^3*z^3/81 + 2*y^2*z^4/81 + 5*y*z^5/81 + 2*z^6/81) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * x^4 * (y - x)^2 + (1/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (1/3 : ℝ) * x^4 * (z - y)^2 + (4/9 : ℝ) * x^3 * (y - x)^3 + (2/3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (2 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (8/9 : ℝ) * x^3 * (z - y)^3 + (1/3 : ℝ) * x^2 * (y - x)^4 + (2/3 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (11/3 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (10/3 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^2 * (z - y)^4 + (32/81 : ℝ) * x^1 * (y - x)^5 + (80/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (248/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (292/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (136/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (22/81 : ℝ) * x^1 * (z - y)^5 + (16/81 : ℝ) * (y - x)^6 + (16/27 : ℝ) * (y - x)^5 * (z - y)^1 + (88/81 : ℝ) * (y - x)^4 * (z - y)^2 + (32/27 : ℝ) * (y - x)^3 * (z - y)^3 + (19/27 : ℝ) * (y - x)^2 * (z - y)^4 + (17/81 : ℝ) * (y - x)^1 * (z - y)^5 + (2/81 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^6/81 + 5*x^5*y/81 + 5*x^5*z/81 + 2*x^4*y^2/81 - x^4*y*z/27 + 2*x^4*z^2/81 - 2*x^3*y^3/81 - 34*x^3*y^2*z/81 - 34*x^3*y*z^2/81 - 2*x^3*z^3/81 + 2*x^2*y^4/81 - 34*x^2*y^3*z/81 + 19*x^2*y^2*z^2/9 - 34*x^2*y*z^3/81 + 2*x^2*z^4/81 + 5*x*y^5/81 - x*y^4*z/27 - 34*x*y^3*z^2/81 - 34*x*y^2*z^3/81 - x*y*z^4/27 + 5*x*z^5/81 + 2*y^6/81 + 5*y^5*z/81 + 2*y^4*z^2/81 - 2*y^3*z^3/81 + 2*y^2*z^4/81 + 5*y*z^5/81 + 2*z^6/81) := by
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
  have he : (3*x^2*y^2*z^2 - 7*x*y - 7*x*z - 7*y*z + 18) = (2*x^6/81 + 5*x^5*y/81 + 5*x^5*z/81 + 2*x^4*y^2/81 - x^4*y*z/27 + 2*x^4*z^2/81 - 2*x^3*y^3/81 - 34*x^3*y^2*z/81 - 34*x^3*y*z^2/81 - 2*x^3*z^3/81 + 2*x^2*y^4/81 - 34*x^2*y^3*z/81 + 19*x^2*y^2*z^2/9 - 34*x^2*y*z^3/81 + 2*x^2*z^4/81 + 5*x*y^5/81 - x*y^4*z/27 - 34*x*y^3*z^2/81 - 34*x*y^2*z^3/81 - x*y*z^4/27 + 5*x*z^5/81 + 2*y^6/81 + 5*y^5*z/81 + 2*y^4*z^2/81 - 2*y^3*z^3/81 + 2*y^2*z^4/81 + 5*y*z^5/81 + 2*z^6/81) := by
    linear_combination (-2*x^5/81 - x^4*y/27 - x^4*z/27 - 2*x^4/27 + x^3*y^2/81 + x^3*y*z/9 - x^3*y/27 + x^3*z^2/81 - x^3*z/27 - 2*x^3/9 + x^2*y^3/81 + 8*x^2*y^2*z/27 + 2*x^2*y^2/27 + 8*x^2*y*z^2/27 + 11*x^2*y*z/27 + x^2*y/9 + x^2*z^3/81 + 2*x^2*z^2/27 + x^2*z/9 - 2*x^2/3 - x*y^4/27 + x*y^3*z/9 - x*y^3/27 + 8*x*y^2*z^2/27 + 11*x*y^2*z/27 + x*y^2/9 + x*y*z^3/9 + 11*x*y*z^2/27 + x*y*z + x*y - x*z^4/27 - x*z^3/27 + x*z^2/9 + x*z - 2*x - 2*y^5/81 - y^4*z/27 - 2*y^4/27 + y^3*z^2/81 - y^3*z/27 - 2*y^3/9 + y^2*z^3/81 + 2*y^2*z^2/27 + y^2*z/9 - 2*y^2/3 - y*z^4/27 - y*z^3/27 + y*z^2/9 + y*z - 2*y - 2*z^5/81 - 2*z^4/27 - 2*z^3/9 - 2*z^2/3 - 2*z - 6) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 3), 7 * (x * y + y * z + z * x) ≤ 18 + 3 * (x * y * z) ^ 2) := @solution
#print axioms solution
