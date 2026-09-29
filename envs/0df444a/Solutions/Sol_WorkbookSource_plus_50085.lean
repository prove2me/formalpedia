-- Prove2me | solution 1 for WorkbookSource.plus_50085
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:57.738424+00:00
-- url     : https://prove2.me/submissions/69d6813c-d901-43de-a4f5-4d56b7fd7516

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * (y - z) / (2 * x + y) ^ 2 + y * (z - x) / (2 * y + z) ^ 2 + z * (x - y) / (2 * z + x) ^ 2 + 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)) ≥ 1 / 3   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^6*y^2 + 4*x^6*y*z + 4*x^6*z^2 - 12*x^5*y^3 - 12*x^5*y^2*z + 12*x^5*y*z^2 + 12*x^5*z^3 + 13*x^4*y^4 - 19*x^4*y^3*z + 56*x^4*y*z^3 + 13*x^4*z^4 + 12*x^3*y^5 + 56*x^3*y^4*z - 62*x^3*y^3*z^2 - 62*x^3*y^2*z^3 - 19*x^3*y*z^4 - 12*x^3*z^5 + 4*x^2*y^6 + 12*x^2*y^5*z - 62*x^2*y^3*z^3 - 12*x^2*y*z^5 + 4*x^2*z^6 + 4*x*y^6*z - 12*x*y^5*z^2 - 19*x*y^4*z^3 + 56*x*y^3*z^4 + 12*x*y^2*z^5 + 4*x*y*z^6 + 4*y^6*z^2 - 12*y^5*z^3 + 13*y^4*z^4 + 12*y^3*z^5 + 4*y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (243 : ℝ) * x^6 * (y - x)^2 + (243 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (243 : ℝ) * x^6 * (z - y)^2 + (1053 : ℝ) * x^5 * (y - x)^3 + (1944 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (1701 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (405 : ℝ) * x^5 * (z - y)^3 + (1863 : ℝ) * x^4 * (y - x)^4 + (4941 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (5184 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (2106 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (243 : ℝ) * x^4 * (z - y)^4 + (1710 : ℝ) * x^3 * (y - x)^5 + (5805 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (7524 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (4266 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (981 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (72 : ℝ) * x^3 * (z - y)^5 + (849 : ℝ) * x^2 * (y - x)^6 + (3444 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (5379 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (3918 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (1326 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (192 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (12 : ℝ) * x^2 * (z - y)^6 + (213 : ℝ) * x^1 * (y - x)^7 + (987 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (1803 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (1605 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (708 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (144 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (12 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (21 : ℝ) * (y - x)^8 + (108 : ℝ) * (y - x)^7 * (z - y)^1 + (226 : ℝ) * (y - x)^6 * (z - y)^2 + (240 : ℝ) * (y - x)^5 * (z - y)^3 + (133 : ℝ) * (y - x)^4 * (z - y)^4 + (36 : ℝ) * (y - x)^3 * (z - y)^5 + (4 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (4*x^6*y^2 + 4*x^6*y*z + 4*x^6*z^2 - 12*x^5*y^3 - 12*x^5*y^2*z + 12*x^5*y*z^2 + 12*x^5*z^3 + 13*x^4*y^4 - 19*x^4*y^3*z + 56*x^4*y*z^3 + 13*x^4*z^4 + 12*x^3*y^5 + 56*x^3*y^4*z - 62*x^3*y^3*z^2 - 62*x^3*y^2*z^3 - 19*x^3*y*z^4 - 12*x^3*z^5 + 4*x^2*y^6 + 12*x^2*y^5*z - 62*x^2*y^3*z^3 - 12*x^2*y*z^5 + 4*x^2*z^6 + 4*x*y^6*z - 12*x*y^5*z^2 - 19*x*y^4*z^3 + 56*x*y^3*z^4 + 12*x*y^2*z^5 + 4*x*y*z^6 + 4*y^6*z^2 - 12*y^5*z^3 + 13*y^4*z^4 + 12*y^3*z^5 + 4*y^2*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (243 : ℝ) * x^6 * (z - x)^2 + (243 : ℝ) * x^6 * (z - x)^1 * (y - z)^1 + (243 : ℝ) * x^6 * (y - z)^2 + (1053 : ℝ) * x^5 * (z - x)^3 + (1215 : ℝ) * x^5 * (z - x)^2 * (y - z)^1 + (972 : ℝ) * x^5 * (z - x)^1 * (y - z)^2 + (405 : ℝ) * x^5 * (y - z)^3 + (1863 : ℝ) * x^4 * (z - x)^4 + (2511 : ℝ) * x^4 * (z - x)^3 * (y - z)^1 + (1539 : ℝ) * x^4 * (z - x)^2 * (y - z)^2 + (891 : ℝ) * x^4 * (z - x)^1 * (y - z)^3 + (243 : ℝ) * x^4 * (y - z)^4 + (1710 : ℝ) * x^3 * (z - x)^5 + (2745 : ℝ) * x^3 * (z - x)^4 * (y - z)^1 + (1404 : ℝ) * x^3 * (z - x)^3 * (y - z)^2 + (576 : ℝ) * x^3 * (z - x)^2 * (y - z)^3 + (351 : ℝ) * x^3 * (z - x)^1 * (y - z)^4 + (72 : ℝ) * x^3 * (y - z)^5 + (849 : ℝ) * x^2 * (z - x)^6 + (1650 : ℝ) * x^2 * (z - x)^5 * (y - z)^1 + (894 : ℝ) * x^2 * (z - x)^4 * (y - z)^2 + (138 : ℝ) * x^2 * (z - x)^3 * (y - z)^3 + (141 : ℝ) * x^2 * (z - x)^2 * (y - z)^4 + (96 : ℝ) * x^2 * (z - x)^1 * (y - z)^5 + (12 : ℝ) * x^2 * (y - z)^6 + (213 : ℝ) * x^1 * (z - x)^7 + (504 : ℝ) * x^1 * (z - x)^6 * (y - z)^1 + (354 : ℝ) * x^1 * (z - x)^5 * (y - z)^2 + (60 : ℝ) * x^1 * (z - x)^4 * (y - z)^3 + (33 : ℝ) * x^1 * (z - x)^3 * (y - z)^4 + (48 : ℝ) * x^1 * (z - x)^2 * (y - z)^5 + (12 : ℝ) * x^1 * (z - x)^1 * (y - z)^6 + (21 : ℝ) * (z - x)^8 + (60 : ℝ) * (z - x)^7 * (y - z)^1 + (58 : ℝ) * (z - x)^6 * (y - z)^2 + (24 : ℝ) * (z - x)^5 * (y - z)^3 + (13 : ℝ) * (z - x)^4 * (y - z)^4 + (12 : ℝ) * (z - x)^3 * (y - z)^5 + (4 : ℝ) * (z - x)^2 * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^6*y^2 + 4*x^6*y*z + 4*x^6*z^2 - 12*x^5*y^3 - 12*x^5*y^2*z + 12*x^5*y*z^2 + 12*x^5*z^3 + 13*x^4*y^4 - 19*x^4*y^3*z + 56*x^4*y*z^3 + 13*x^4*z^4 + 12*x^3*y^5 + 56*x^3*y^4*z - 62*x^3*y^3*z^2 - 62*x^3*y^2*z^3 - 19*x^3*y*z^4 - 12*x^3*z^5 + 4*x^2*y^6 + 12*x^2*y^5*z - 62*x^2*y^3*z^3 - 12*x^2*y*z^5 + 4*x^2*z^6 + 4*x*y^6*z - 12*x*y^5*z^2 - 19*x*y^4*z^3 + 56*x*y^3*z^4 + 12*x*y^2*z^5 + 4*x*y*z^6 + 4*y^6*z^2 - 12*y^5*z^3 + 13*y^4*z^4 + 12*y^3*z^5 + 4*y^2*z^6) := by
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
  have hn : 0 ≤ (4*x^6*y^2 + 4*x^6*y*z + 4*x^6*z^2 - 12*x^5*y^3 - 12*x^5*y^2*z + 12*x^5*y*z^2 + 12*x^5*z^3 + 13*x^4*y^4 - 19*x^4*y^3*z + 56*x^4*y*z^3 + 13*x^4*z^4 + 12*x^3*y^5 + 56*x^3*y^4*z - 62*x^3*y^3*z^2 - 62*x^3*y^2*z^3 - 19*x^3*y*z^4 - 12*x^3*z^5 + 4*x^2*y^6 + 12*x^2*y^5*z - 62*x^2*y^3*z^3 - 12*x^2*y*z^5 + 4*x^2*z^6 + 4*x*y^6*z - 12*x*y^5*z^2 - 19*x*y^4*z^3 + 56*x*y^3*z^4 + 12*x*y^2*z^5 + 4*x*y*z^6 + 4*y^6*z^2 - 12*y^5*z^3 + 13*y^4*z^4 + 12*y^3*z^5 + 4*y^2*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * (y - z) / (2 * x + y) ^ 2 + y * (z - x) / (2 * y + z) ^ 2 + z * (x - y) / (2 * z + x) ^ 2 + 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)) ≥ 1 / 3) := @solution
#print axioms solution
