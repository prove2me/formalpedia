-- Prove2me | solution 1 for WorkbookSource.base_32804
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:53.814347+00:00
-- url     : https://prove2.me/submissions/c6d908ae-5f9b-4571-b19c-5aea839ec4c1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + z / x + 243 * x * y * z / (2 * (x + y + z) ^ 3 + 27 * x * y * z)) ≥ 6  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5*z + 2*x^4*y^2 - 6*x^4*y*z + 6*x^4*z^2 + 6*x^3*y^3 - 24*x^3*y^2*z + 5*x^3*y*z^2 + 6*x^3*z^3 + 6*x^2*y^4 + 5*x^2*y^3*z + 27*x^2*y^2*z^2 - 24*x^2*y*z^3 + 2*x^2*z^4 + 2*x*y^5 - 6*x*y^4*z - 24*x*y^3*z^2 + 5*x*y^2*z^3 - 6*x*y*z^4 + 2*y^4*z^2 + 6*y^3*z^3 + 6*y^2*z^4 + 2*y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * x^4 * (y - x)^2 + (27 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (27 : ℝ) * x^4 * (z - y)^2 + (87 : ℝ) * x^3 * (y - x)^3 + (171 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (126 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (21 : ℝ) * x^3 * (z - y)^3 + (111 : ℝ) * x^2 * (y - x)^4 + (303 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (288 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (96 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (12 : ℝ) * x^2 * (z - y)^4 + (67 : ℝ) * x^1 * (y - x)^5 + (217 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (259 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (131 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (26 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^1 * (z - y)^5 + (16 : ℝ) * (y - x)^6 + (56 : ℝ) * (y - x)^5 * (z - y)^1 + (76 : ℝ) * (y - x)^4 * (z - y)^2 + (50 : ℝ) * (y - x)^3 * (z - y)^3 + (16 : ℝ) * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (2*x^5*z + 2*x^4*y^2 - 6*x^4*y*z + 6*x^4*z^2 + 6*x^3*y^3 - 24*x^3*y^2*z + 5*x^3*y*z^2 + 6*x^3*z^3 + 6*x^2*y^4 + 5*x^2*y^3*z + 27*x^2*y^2*z^2 - 24*x^2*y*z^3 + 2*x^2*z^4 + 2*x*y^5 - 6*x*y^4*z - 24*x*y^3*z^2 + 5*x*y^2*z^3 - 6*x*y*z^4 + 2*y^4*z^2 + 6*y^3*z^3 + 6*y^2*z^4 + 2*y*z^5) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * x^4 * (z - x)^2 + (27 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (27 : ℝ) * x^4 * (y - z)^2 + (87 : ℝ) * x^3 * (z - x)^3 + (90 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (45 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (21 : ℝ) * x^3 * (y - z)^3 + (111 : ℝ) * x^2 * (z - x)^4 + (141 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (45 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (15 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (12 : ℝ) * x^2 * (y - z)^4 + (67 : ℝ) * x^1 * (z - x)^5 + (118 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (61 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (14 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (8 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (2 : ℝ) * x^1 * (y - z)^5 + (16 : ℝ) * (z - x)^6 + (40 : ℝ) * (z - x)^5 * (y - z)^1 + (36 : ℝ) * (z - x)^4 * (y - z)^2 + (14 : ℝ) * (z - x)^3 * (y - z)^3 + (2 : ℝ) * (z - x)^2 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5*z + 2*x^4*y^2 - 6*x^4*y*z + 6*x^4*z^2 + 6*x^3*y^3 - 24*x^3*y^2*z + 5*x^3*y*z^2 + 6*x^3*z^3 + 6*x^2*y^4 + 5*x^2*y^3*z + 27*x^2*y^2*z^2 - 24*x^2*y*z^3 + 2*x^2*z^4 + 2*x*y^5 - 6*x*y^4*z - 24*x*y^3*z^2 + 5*x*y^2*z^3 - 6*x*y*z^4 + 2*y^4*z^2 + 6*y^3*z^3 + 6*y^2*z^4 + 2*y*z^5) := by
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
  have hn : 0 ≤ (2*x^5*z + 2*x^4*y^2 - 6*x^4*y*z + 6*x^4*z^2 + 6*x^3*y^3 - 24*x^3*y^2*z + 5*x^3*y*z^2 + 6*x^3*z^3 + 6*x^2*y^4 + 5*x^2*y^3*z + 27*x^2*y^2*z^2 - 24*x^2*y*z^3 + 2*x^2*z^4 + 2*x*y^5 - 6*x*y^4*z - 24*x*y^3*z^2 + 5*x*y^2*z^3 - 6*x*y*z^4 + 2*y^4*z^2 + 6*y^3*z^3 + 6*y^2*z^4 + 2*y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / y + y / z + z / x + 243 * x * y * z / (2 * (x + y + z) ^ 3 + 27 * x * y * z)) ≥ 6) := @solution
#print axioms solution
