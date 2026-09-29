-- Prove2me | solution 1 for WorkbookSource.plus_73163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:23.438986+00:00
-- url     : https://prove2.me/submissions/1f891417-d624-4a55-90d2-85619091c1be

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / (3 * x ^ 2 + 2 * y ^ 2 + z ^ 2) + y * z / (3 * y ^ 2 + 2 * z ^ 2 + x ^ 2) + z * x / (3 * z ^ 2 + 2 * x ^ 2 + y ^ 2)) ≤ 1 / 2   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (6*x^6 - 4*x^5*y - 6*x^5*z + 25*x^4*y^2 - 12*x^4*y*z + 23*x^4*z^2 - 14*x^3*y^3 - 22*x^3*y^2*z - 14*x^3*y*z^2 - 14*x^3*z^3 + 23*x^2*y^4 - 14*x^2*y^3*z + 54*x^2*y^2*z^2 - 22*x^2*y*z^3 + 25*x^2*z^4 - 6*x*y^5 - 12*x*y^4*z - 22*x*y^3*z^2 - 14*x*y^2*z^3 - 12*x*y*z^4 - 4*x*z^5 + 6*y^6 - 4*y^5*z + 25*y^4*z^2 - 14*y^3*z^3 + 23*y^2*z^4 - 6*y*z^5 + 6*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (80 : ℝ) * x^4 * (y - x)^2 + (80 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (80 : ℝ) * x^4 * (z - y)^2 + (220 : ℝ) * x^3 * (y - x)^3 + (316 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (296 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (100 : ℝ) * x^3 * (z - y)^3 + (256 : ℝ) * x^2 * (y - x)^4 + (484 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (516 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (288 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (76 : ℝ) * x^2 * (z - y)^4 + (146 : ℝ) * x^1 * (y - x)^5 + (344 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (428 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (312 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (134 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (26 : ℝ) * x^1 * (z - y)^5 + (36 : ℝ) * (y - x)^6 + (102 : ℝ) * (y - x)^5 * (z - y)^1 + (151 : ℝ) * (y - x)^4 * (z - y)^2 + (138 : ℝ) * (y - x)^3 * (z - y)^3 + (83 : ℝ) * (y - x)^2 * (z - y)^4 + (30 : ℝ) * (y - x)^1 * (z - y)^5 + (6 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (6*x^6 - 4*x^5*y - 6*x^5*z + 25*x^4*y^2 - 12*x^4*y*z + 23*x^4*z^2 - 14*x^3*y^3 - 22*x^3*y^2*z - 14*x^3*y*z^2 - 14*x^3*z^3 + 23*x^2*y^4 - 14*x^2*y^3*z + 54*x^2*y^2*z^2 - 22*x^2*y*z^3 + 25*x^2*z^4 - 6*x*y^5 - 12*x*y^4*z - 22*x*y^3*z^2 - 14*x*y^2*z^3 - 12*x*y*z^4 - 4*x*z^5 + 6*y^6 - 4*y^5*z + 25*y^4*z^2 - 14*y^3*z^3 + 23*y^2*z^4 - 6*y*z^5 + 6*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (80 : ℝ) * x^4 * (z - x)^2 + (80 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (80 : ℝ) * x^4 * (y - z)^2 + (220 : ℝ) * x^3 * (z - x)^3 + (344 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (324 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (100 : ℝ) * x^3 * (y - z)^3 + (256 : ℝ) * x^2 * (z - x)^4 + (540 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (600 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (316 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (76 : ℝ) * x^2 * (y - z)^4 + (146 : ℝ) * x^1 * (z - x)^5 + (386 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (512 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (368 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (148 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (26 : ℝ) * x^1 * (y - z)^5 + (36 : ℝ) * (z - x)^6 + (114 : ℝ) * (z - x)^5 * (y - z)^1 + (181 : ℝ) * (z - x)^4 * (y - z)^2 + (166 : ℝ) * (z - x)^3 * (y - z)^3 + (95 : ℝ) * (z - x)^2 * (y - z)^4 + (32 : ℝ) * (z - x)^1 * (y - z)^5 + (6 : ℝ) * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*x^6 - 4*x^5*y - 6*x^5*z + 25*x^4*y^2 - 12*x^4*y*z + 23*x^4*z^2 - 14*x^3*y^3 - 22*x^3*y^2*z - 14*x^3*y*z^2 - 14*x^3*z^3 + 23*x^2*y^4 - 14*x^2*y^3*z + 54*x^2*y^2*z^2 - 22*x^2*y*z^3 + 25*x^2*z^4 - 6*x*y^5 - 12*x*y^4*z - 22*x*y^3*z^2 - 14*x*y^2*z^3 - 12*x*y*z^4 - 4*x*z^5 + 6*y^6 - 4*y^5*z + 25*y^4*z^2 - 14*y^3*z^3 + 23*y^2*z^4 - 6*y*z^5 + 6*z^6) := by
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
  have hn : 0 ≤ (6*x^6 - 4*x^5*y - 6*x^5*z + 25*x^4*y^2 - 12*x^4*y*z + 23*x^4*z^2 - 14*x^3*y^3 - 22*x^3*y^2*z - 14*x^3*y*z^2 - 14*x^3*z^3 + 23*x^2*y^4 - 14*x^2*y^3*z + 54*x^2*y^2*z^2 - 22*x^2*y*z^3 + 25*x^2*z^4 - 6*x*y^5 - 12*x*y^4*z - 22*x*y^3*z^2 - 14*x*y^2*z^3 - 12*x*y*z^4 - 4*x*z^5 + 6*y^6 - 4*y^5*z + 25*y^4*z^2 - 14*y^3*z^3 + 23*y^2*z^4 - 6*y*z^5 + 6*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y / (3 * x ^ 2 + 2 * y ^ 2 + z ^ 2) + y * z / (3 * y ^ 2 + 2 * z ^ 2 + x ^ 2) + z * x / (3 * z ^ 2 + 2 * x ^ 2 + y ^ 2)) ≤ 1 / 2) := @solution
#print axioms solution
