-- Prove2me | solution 1 for WorkbookSource.base_12676
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:26.039874+00:00
-- url     : https://prove2.me/submissions/f22d1389-3cf3-4f80-9b38-fbf14f98ee72

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : x / (x ^ 2 + y + z) + y / (y ^ 2 + z + x) + z / (z ^ 2 + x + y) ≤ 1  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^6/27 + x^5*y/9 + x^5*z/9 + x^4*y^2/9 + 2*x^4*y*z/27 + x^4*z^2/9 + 4*x^3*y^3/27 - x^3*y^2*z/3 - x^3*y*z^2/3 + 4*x^3*z^3/27 + x^2*y^4/9 - x^2*y^3*z/3 - 2*x^2*y^2*z^2/9 - x^2*y*z^3/3 + x^2*z^4/9 + x*y^5/9 + 2*x*y^4*z/27 - x*y^3*z^2/3 - x*y^2*z^3/3 + 2*x*y*z^4/27 + x*z^5/9 + 2*y^6/27 + y^5*z/9 + y^4*z^2/9 + 4*y^3*z^3/27 + y^2*z^4/9 + y*z^5/9 + 2*z^6/27) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * x^4 * (y - x)^2 + (10/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (10/3 : ℝ) * x^4 * (z - y)^2 + (238/27 : ℝ) * x^3 * (y - x)^3 + (119/9 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (121/9 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (122/27 : ℝ) * x^3 * (z - y)^3 + (242/27 : ℝ) * x^2 * (y - x)^4 + (484/27 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (187/9 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (319/27 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (68/27 : ℝ) * x^2 * (z - y)^4 + (112/27 : ℝ) * x^1 * (y - x)^5 + (280/27 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (14 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (287/27 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (113/27 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (2/3 : ℝ) * x^1 * (z - y)^5 + (20/27 : ℝ) * (y - x)^6 + (20/9 : ℝ) * (y - x)^5 * (z - y)^1 + (31/9 : ℝ) * (y - x)^4 * (z - y)^2 + (86/27 : ℝ) * (y - x)^3 * (z - y)^3 + (16/9 : ℝ) * (y - x)^2 * (z - y)^4 + (5/9 : ℝ) * (y - x)^1 * (z - y)^5 + (2/27 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^6/27 + x^5*y/9 + x^5*z/9 + x^4*y^2/9 + 2*x^4*y*z/27 + x^4*z^2/9 + 4*x^3*y^3/27 - x^3*y^2*z/3 - x^3*y*z^2/3 + 4*x^3*z^3/27 + x^2*y^4/9 - x^2*y^3*z/3 - 2*x^2*y^2*z^2/9 - x^2*y*z^3/3 + x^2*z^4/9 + x*y^5/9 + 2*x*y^4*z/27 - x*y^3*z^2/3 - x*y^2*z^3/3 + 2*x*y*z^4/27 + x*z^5/9 + 2*y^6/27 + y^5*z/9 + y^4*z^2/9 + 4*y^3*z^3/27 + y^2*z^4/9 + y*z^5/9 + 2*z^6/27) := by
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
  have he : (x^4 + x^3*y^2 + x^3*z^2 - x^3 + x^2*y^3 + x^2*y^2*z^2 - x^2*y^2*z - 2*x^2*y^2 - x^2*y*z^2 + x^2*y*z + x^2*z^3 - 2*x^2*z^2 - x*y^2*z^2 + x*y^2*z + x*y*z^2 - x*y*z + y^4 + y^3*z^2 - y^3 + y^2*z^3 - 2*y^2*z^2 + z^4 - z^3) = (2*x^6/27 + x^5*y/9 + x^5*z/9 + x^4*y^2/9 + 2*x^4*y*z/27 + x^4*z^2/9 + 4*x^3*y^3/27 - x^3*y^2*z/3 - x^3*y*z^2/3 + 4*x^3*z^3/27 + x^2*y^4/9 - x^2*y^3*z/3 - 2*x^2*y^2*z^2/9 - x^2*y*z^3/3 + x^2*z^4/9 + x*y^5/9 + 2*x*y^4*z/27 - x*y^3*z^2/3 - x*y^2*z^3/3 + 2*x*y*z^4/27 + x*z^5/9 + 2*y^6/27 + y^5*z/9 + y^4*z^2/9 + 4*y^3*z^3/27 + y^2*z^4/9 + y*z^5/9 + 2*z^6/27) := by
    linear_combination (-2*x^5/27 - x^4*y/27 - x^4*z/27 - 2*x^4/9 - 2*x^3*y^2/27 + x^3*y/9 - 2*x^3*z^2/27 + x^3*z/9 + x^3/3 - 2*x^2*y^3/27 + 11*x^2*y^2*z/27 + 2*x^2*y^2/3 + 11*x^2*y*z^2/27 - 2*x^2*y*z/9 - 2*x^2*z^3/27 + 2*x^2*z^2/3 - x*y^4/27 + x*y^3/9 + 11*x*y^2*z^2/27 - 2*x*y^2*z/9 - 2*x*y*z^2/9 + x*y*z/3 - x*z^4/27 + x*z^3/9 - 2*y^5/27 - y^4*z/27 - 2*y^4/9 - 2*y^3*z^2/27 + y^3*z/9 + y^3/3 - 2*y^2*z^3/27 + 2*y^2*z^2/3 - y*z^4/27 + y*z^3/9 - 2*z^5/27 - 2*z^4/9 + z^3/3) * h
  have hn : 0 ≤ (x^4 + x^3*y^2 + x^3*z^2 - x^3 + x^2*y^3 + x^2*y^2*z^2 - x^2*y^2*z - 2*x^2*y^2 - x^2*y*z^2 + x^2*y*z + x^2*z^3 - 2*x^2*z^2 - x*y^2*z^2 + x*y^2*z + x*y*z^2 - x*y*z + y^4 + y^3*z^2 - y^3 + y^2*z^3 - 2*y^2*z^2 + z^4 - z^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), x / (x ^ 2 + y + z) + y / (y ^ 2 + z + x) + z / (z ^ 2 + x + y) ≤ 1) := @solution
#print axioms solution
