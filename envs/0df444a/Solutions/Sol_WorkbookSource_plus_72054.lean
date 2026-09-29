-- Prove2me | solution 1 for WorkbookSource.plus_72054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:22.840208+00:00
-- url     : https://prove2.me/submissions/b8fc297a-fe36-4cfd-a998-478a45deaa43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) + (x * y + y * z + z * x) / 2 ≤ 3   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5/81 + 10*x^4*y/81 + 10*x^4*z/81 - 7*x^3*y^2/81 + 40*x^3*y*z/81 - 7*x^3*z^2/81 - 7*x^2*y^3/81 - 16*x^2*y^2*z/27 - 16*x^2*y*z^2/27 - 7*x^2*z^3/81 + 10*x*y^4/81 + 40*x*y^3*z/81 - 16*x*y^2*z^2/27 + 40*x*y*z^3/81 + 10*x*z^4/81 + 2*y^5/81 + 10*y^4*z/81 - 7*y^3*z^2/81 - 7*y^2*z^3/81 + 10*y*z^4/81 + 2*z^5/81) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * x^3 * (y - x)^2 + (4/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (4/3 : ℝ) * x^3 * (z - y)^2 + (22/9 : ℝ) * x^2 * (y - x)^3 + (11/3 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (13/3 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (14/9 : ℝ) * x^2 * (z - y)^3 + (34/27 : ℝ) * x^1 * (y - x)^4 + (68/27 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (32/9 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (62/27 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (10/27 : ℝ) * x^1 * (z - y)^4 + (10/81 : ℝ) * (y - x)^5 + (25/81 : ℝ) * (y - x)^4 * (z - y)^1 + (52/81 : ℝ) * (y - x)^3 * (z - y)^2 + (53/81 : ℝ) * (y - x)^2 * (z - y)^3 + (20/81 : ℝ) * (y - x)^1 * (z - y)^4 + (2/81 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5/81 + 10*x^4*y/81 + 10*x^4*z/81 - 7*x^3*y^2/81 + 40*x^3*y*z/81 - 7*x^3*z^2/81 - 7*x^2*y^3/81 - 16*x^2*y^2*z/27 - 16*x^2*y*z^2/27 - 7*x^2*z^3/81 + 10*x*y^4/81 + 40*x*y^3*z/81 - 16*x*y^2*z^2/27 + 40*x*y*z^3/81 + 10*x*z^4/81 + 2*y^5/81 + 10*y^4*z/81 - 7*y^3*z^2/81 - 7*y^2*z^3/81 + 10*y*z^4/81 + 2*z^5/81) := by
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
  have he : (-x^2*y^2*z - x^2*y^2 - x^2*y*z^2 - 2*x^2*y*z - x^2*y - x^2*z^2 - x^2*z - x*y^2*z^2 - 2*x*y^2*z - x*y^2 - 2*x*y*z^2 + 3*x*y*z + 3*x*y - x*z^2 + 3*x*z + 2*x - y^2*z^2 - y^2*z - y*z^2 + 3*y*z + 2*y + 2*z) = (2*x^5/81 + 10*x^4*y/81 + 10*x^4*z/81 - 7*x^3*y^2/81 + 40*x^3*y*z/81 - 7*x^3*z^2/81 - 7*x^2*y^3/81 - 16*x^2*y^2*z/27 - 16*x^2*y*z^2/27 - 7*x^2*z^3/81 + 10*x*y^4/81 + 40*x*y^3*z/81 - 16*x*y^2*z^2/27 + 40*x*y*z^3/81 + 10*x*z^4/81 + 2*y^5/81 + 10*y^4*z/81 - 7*y^3*z^2/81 - 7*y^2*z^3/81 + 10*y*z^4/81 + 2*z^5/81) := by
    linear_combination (-2*x^4/81 - 8*x^3*y/81 - 8*x^3*z/81 - 2*x^3/27 + 5*x^2*y^2/27 - 8*x^2*y*z/27 - 2*x^2*y/9 + 5*x^2*z^2/27 - 2*x^2*z/9 - 2*x^2/9 - 8*x*y^3/81 - 8*x*y^2*z/27 - 2*x*y^2/9 - 8*x*y*z^2/27 - 22*x*y*z/9 - 13*x*y/9 - 8*x*z^3/81 - 2*x*z^2/9 - 13*x*z/9 - 2*x/3 - 2*y^4/81 - 8*y^3*z/81 - 2*y^3/27 + 5*y^2*z^2/27 - 2*y^2*z/9 - 2*y^2/9 - 8*y*z^3/81 - 2*y*z^2/9 - 13*y*z/9 - 2*y/3 - 2*z^4/81 - 2*z^3/27 - 2*z^2/9 - 2*z/3) * h
  have hn : 0 ≤ (-x^2*y^2*z - x^2*y^2 - x^2*y*z^2 - 2*x^2*y*z - x^2*y - x^2*z^2 - x^2*z - x*y^2*z^2 - 2*x*y^2*z - x*y^2 - 2*x*y*z^2 + 3*x*y*z + 3*x*y - x*z^2 + 3*x*z + 2*x - y^2*z^2 - y^2*z - y*z^2 + 3*y*z + 2*y + 2*z) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) + (x * y + y * z + z * x) / 2 ≤ 3) := @solution
#print axioms solution
