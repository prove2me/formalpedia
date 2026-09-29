-- Prove2me | solution 1 for WorkbookSource.plus_9349
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:21:23.805582+00:00
-- url     : https://prove2.me/submissions/0fac9d42-6c42-4edf-954f-e1e9ed20ff3a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (3 * y ^ 2 + 3 * z ^ 2 - 4 * y * z) * x ^ 5 + (y + z) * (16 * z ^ 2 - 21 * y * z + 16 * y ^ 2) * x ^ 4 + (-38 * y ^ 2 * z ^ 2 + 18 * y ^ 3 * z + 27 * y ^ 4 + 27 * z ^ 4 + 18 * y * z ^ 3) * x ^ 3 + (y + z) * (19 * z ^ 4 + 3 * y * z ^ 3 - 70 * y ^ 2 * z ^ 2 + 3 * y ^ 3 * z + 19 * y ^ 4) * x ^ 2 + (10 * y ^ 5 * z - 41 * y ^ 2 * z ^ 4 + 10 * y * z ^ 5 + 6 * y ^ 6 - 100 * y ^ 3 * z ^ 3 - 41 * y ^ 4 * z ^ 2 + 6 * z ^ 6) * x + (y + z) * (z ^ 2 + y * z + y ^ 2) * (z ^ 4 + 5 * y * z ^ 3 + 9 * y ^ 2 * z ^ 2 + 5 * y ^ 3 * z + y ^ 4) ≥ 0   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^5*y^2 - 4*x^5*y*z + 3*x^5*z^2 + 16*x^4*y^3 - 5*x^4*y^2*z - 5*x^4*y*z^2 + 16*x^4*z^3 + 27*x^3*y^4 + 18*x^3*y^3*z - 38*x^3*y^2*z^2 + 18*x^3*y*z^3 + 27*x^3*z^4 + 19*x^2*y^5 + 22*x^2*y^4*z - 67*x^2*y^3*z^2 - 67*x^2*y^2*z^3 + 22*x^2*y*z^4 + 19*x^2*z^5 + 6*x*y^6 + 10*x*y^5*z - 41*x*y^4*z^2 - 100*x*y^3*z^3 - 41*x*y^2*z^4 + 10*x*y*z^5 + 6*x*z^6 + y^7 + 7*y^6*z + 21*y^5*z^2 + 34*y^4*z^3 + 34*y^3*z^4 + 21*y^2*z^5 + 7*y*z^6 + z^7) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * x^5 * (y - x)^2 + (256 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (544 : ℝ) * x^5 * (z - y)^2 + (1120 : ℝ) * x^4 * (y - x)^3 + (1680 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (2288 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (864 : ℝ) * x^4 * (z - y)^3 + (1952 : ℝ) * x^3 * (y - x)^4 + (3904 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (4588 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (2636 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (522 : ℝ) * x^3 * (z - y)^4 + (1694 : ℝ) * x^2 * (y - x)^5 + (4235 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (5096 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (3409 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (1152 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (149 : ℝ) * x^2 * (z - y)^5 + (732 : ℝ) * x^1 * (y - x)^6 + (2196 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (2918 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (2176 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (936 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (214 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (20 : ℝ) * x^1 * (z - y)^6 + (126 : ℝ) * (y - x)^7 + (441 : ℝ) * (y - x)^6 * (z - y)^1 + (663 : ℝ) * (y - x)^5 * (z - y)^2 + (555 : ℝ) * (y - x)^4 * (z - y)^3 + (279 : ℝ) * (y - x)^3 * (z - y)^4 + (84 : ℝ) * (y - x)^2 * (z - y)^5 + (14 : ℝ) * (y - x)^1 * (z - y)^6 + (1 : ℝ) * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (3*x^5*y^2 - 4*x^5*y*z + 3*x^5*z^2 + 16*x^4*y^3 - 5*x^4*y^2*z - 5*x^4*y*z^2 + 16*x^4*z^3 + 27*x^3*y^4 + 18*x^3*y^3*z - 38*x^3*y^2*z^2 + 18*x^3*y*z^3 + 27*x^3*z^4 + 19*x^2*y^5 + 22*x^2*y^4*z - 67*x^2*y^3*z^2 - 67*x^2*y^2*z^3 + 22*x^2*y*z^4 + 19*x^2*z^5 + 6*x*y^6 + 10*x*y^5*z - 41*x*y^4*z^2 - 100*x*y^3*z^3 - 41*x*y^2*z^4 + 10*x*y*z^5 + 6*x*z^6 + y^7 + 7*y^6*z + 21*y^5*z^2 + 34*y^4*z^3 + 34*y^3*z^4 + 21*y^2*z^5 + 7*y*z^6 + z^7) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (544 : ℝ) * y^5 * (x - y)^2 + (832 : ℝ) * y^5 * (x - y)^1 * (z - x)^1 + (544 : ℝ) * y^5 * (z - x)^2 + (1856 : ℝ) * y^4 * (x - y)^3 + (3856 : ℝ) * y^4 * (x - y)^2 * (z - x)^1 + (3024 : ℝ) * y^4 * (x - y)^1 * (z - x)^2 + (864 : ℝ) * y^4 * (z - x)^3 + (2506 : ℝ) * y^3 * (x - y)^4 + (6556 : ℝ) * y^3 * (x - y)^3 * (z - x)^1 + (6468 : ℝ) * y^3 * (x - y)^2 * (z - x)^2 + (2908 : ℝ) * y^3 * (x - y)^1 * (z - x)^3 + (522 : ℝ) * y^3 * (z - x)^4 + (1673 : ℝ) * y^2 * (x - y)^5 + (5259 : ℝ) * y^2 * (x - y)^4 * (z - x)^1 + (6409 : ℝ) * y^2 * (x - y)^3 * (z - x)^2 + (3831 : ℝ) * y^2 * (x - y)^2 * (z - x)^3 + (1159 : ℝ) * y^2 * (x - y)^1 * (z - x)^4 + (149 : ℝ) * y^2 * (z - x)^5 + (552 : ℝ) * y^1 * (x - y)^6 + (2020 : ℝ) * y^1 * (x - y)^5 * (z - x)^1 + (2956 : ℝ) * y^1 * (x - y)^4 * (z - x)^2 + (2222 : ℝ) * y^1 * (x - y)^3 * (z - x)^3 + (918 : ℝ) * y^1 * (x - y)^2 * (z - x)^4 + (204 : ℝ) * y^1 * (x - y)^1 * (z - x)^5 + (20 : ℝ) * y^1 * (z - x)^6 + (72 : ℝ) * (x - y)^7 + (300 : ℝ) * (x - y)^6 * (z - x)^1 + (514 : ℝ) * (x - y)^5 * (z - x)^2 + (469 : ℝ) * (x - y)^4 * (z - x)^3 + (247 : ℝ) * (x - y)^3 * (z - x)^4 + (76 : ℝ) * (x - y)^2 * (z - x)^5 + (13 : ℝ) * (x - y)^1 * (z - x)^6 + (1 : ℝ) * (z - x)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (3*x^5*y^2 - 4*x^5*y*z + 3*x^5*z^2 + 16*x^4*y^3 - 5*x^4*y^2*z - 5*x^4*y*z^2 + 16*x^4*z^3 + 27*x^3*y^4 + 18*x^3*y^3*z - 38*x^3*y^2*z^2 + 18*x^3*y*z^3 + 27*x^3*z^4 + 19*x^2*y^5 + 22*x^2*y^4*z - 67*x^2*y^3*z^2 - 67*x^2*y^2*z^3 + 22*x^2*y*z^4 + 19*x^2*z^5 + 6*x*y^6 + 10*x*y^5*z - 41*x*y^4*z^2 - 100*x*y^3*z^3 - 41*x*y^2*z^4 + 10*x*y*z^5 + 6*x*z^6 + y^7 + 7*y^6*z + 21*y^5*z^2 + 34*y^4*z^3 + 34*y^3*z^4 + 21*y^2*z^5 + 7*y*z^6 + z^7) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (544 : ℝ) * y^5 * (z - y)^2 + (256 : ℝ) * y^5 * (z - y)^1 * (x - z)^1 + (256 : ℝ) * y^5 * (x - z)^2 + (1856 : ℝ) * y^4 * (z - y)^3 + (1712 : ℝ) * y^4 * (z - y)^2 * (x - z)^1 + (880 : ℝ) * y^4 * (z - y)^1 * (x - z)^2 + (160 : ℝ) * y^4 * (x - z)^3 + (2506 : ℝ) * y^3 * (z - y)^4 + (3468 : ℝ) * y^3 * (z - y)^3 * (x - z)^1 + (1836 : ℝ) * y^3 * (z - y)^2 * (x - z)^2 + (384 : ℝ) * y^3 * (z - y)^1 * (x - z)^3 + (32 : ℝ) * y^3 * (x - z)^4 + (1673 : ℝ) * y^2 * (z - y)^5 + (3106 : ℝ) * y^2 * (z - y)^4 * (x - z)^1 + (2103 : ℝ) * y^2 * (z - y)^3 * (x - z)^2 + (572 : ℝ) * y^2 * (z - y)^2 * (x - z)^3 + (53 : ℝ) * y^2 * (z - y)^1 * (x - z)^4 + (2 : ℝ) * y^2 * (x - z)^5 + (552 : ℝ) * y^1 * (z - y)^6 + (1292 : ℝ) * y^1 * (z - y)^5 * (x - z)^1 + (1136 : ℝ) * y^1 * (z - y)^4 * (x - z)^2 + (442 : ℝ) * y^1 * (z - y)^3 * (x - z)^3 + (68 : ℝ) * y^1 * (z - y)^2 * (x - z)^4 + (2 : ℝ) * y^1 * (z - y)^1 * (x - z)^5 + (72 : ℝ) * (z - y)^7 + (204 : ℝ) * (z - y)^6 * (x - z)^1 + (226 : ℝ) * (z - y)^5 * (x - z)^2 + (121 : ℝ) * (z - y)^4 * (x - z)^3 + (31 : ℝ) * (z - y)^3 * (x - z)^4 + (3 : ℝ) * (z - y)^2 * (x - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^5*y^2 - 4*x^5*y*z + 3*x^5*z^2 + 16*x^4*y^3 - 5*x^4*y^2*z - 5*x^4*y*z^2 + 16*x^4*z^3 + 27*x^3*y^4 + 18*x^3*y^3*z - 38*x^3*y^2*z^2 + 18*x^3*y*z^3 + 27*x^3*z^4 + 19*x^2*y^5 + 22*x^2*y^4*z - 67*x^2*y^3*z^2 - 67*x^2*y^2*z^3 + 22*x^2*y*z^4 + 19*x^2*z^5 + 6*x*y^6 + 10*x*y^5*z - 41*x*y^4*z^2 - 100*x*y^3*z^3 - 41*x*y^2*z^4 + 10*x*y*z^5 + 6*x*z^6 + y^7 + 7*y^6*z + 21*y^5*z^2 + 34*y^4*z^3 + 34*y^3*z^4 + 21*y^2*z^5 + 7*y*z^6 + z^7) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux2 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (3 * y ^ 2 + 3 * z ^ 2 - 4 * y * z) * x ^ 5 + (y + z) * (16 * z ^ 2 - 21 * y * z + 16 * y ^ 2) * x ^ 4 + (-38 * y ^ 2 * z ^ 2 + 18 * y ^ 3 * z + 27 * y ^ 4 + 27 * z ^ 4 + 18 * y * z ^ 3) * x ^ 3 + (y + z) * (19 * z ^ 4 + 3 * y * z ^ 3 - 70 * y ^ 2 * z ^ 2 + 3 * y ^ 3 * z + 19 * y ^ 4) * x ^ 2 + (10 * y ^ 5 * z - 41 * y ^ 2 * z ^ 4 + 10 * y * z ^ 5 + 6 * y ^ 6 - 100 * y ^ 3 * z ^ 3 - 41 * y ^ 4 * z ^ 2 + 6 * z ^ 6) * x + (y + z) * (z ^ 2 + y * z + y ^ 2) * (z ^ 4 + 5 * y * z ^ 3 + 9 * y ^ 2 * z ^ 2 + 5 * y ^ 3 * z + y ^ 4) ≥ 0) := @solution
#print axioms solution
