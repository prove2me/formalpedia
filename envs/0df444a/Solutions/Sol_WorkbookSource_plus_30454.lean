-- Prove2me | solution 1 for WorkbookSource.plus_30454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:35:41.416913+00:00
-- url     : https://prove2.me/submissions/ca7924eb-45ea-417e-b26e-df4bb454eb35

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (x + y + z) * (1 / x + 1 / y + 1 / z) ^ 2 ≥ 12 / (x ^ 2 + y * z)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y^3 + 3*x^4*y^2*z + 3*x^4*y*z^2 + x^4*z^3 + 2*x^3*y^3*z - 8*x^3*y^2*z^2 + 2*x^3*y*z^3 + x^2*y^4*z - 8*x^2*y^3*z^2 - 8*x^2*y^2*z^3 + x^2*y*z^4 + 2*x*y^4*z^2 + 4*x*y^3*z^3 + 2*x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * x^5 * (y - x)^2 + (22 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (13 : ℝ) * x^5 * (z - y)^2 + (82 : ℝ) * x^4 * (y - x)^3 + (123 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (73 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (16 : ℝ) * x^4 * (z - y)^3 + (116 : ℝ) * x^3 * (y - x)^4 + (232 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (166 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (50 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^3 * (z - y)^4 + (76 : ℝ) * x^2 * (y - x)^5 + (190 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (168 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (62 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (8 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (22 : ℝ) * x^1 * (y - x)^6 + (66 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (71 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (32 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (5 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^7 + (7 : ℝ) * (y - x)^6 * (z - y)^1 + (9 : ℝ) * (y - x)^5 * (z - y)^2 + (5 : ℝ) * (y - x)^4 * (z - y)^3 + (1 : ℝ) * (y - x)^3 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (x^4*y^3 + 3*x^4*y^2*z + 3*x^4*y*z^2 + x^4*z^3 + 2*x^3*y^3*z - 8*x^3*y^2*z^2 + 2*x^3*y*z^3 + x^2*y^4*z - 8*x^2*y^3*z^2 - 8*x^2*y^2*z^3 + x^2*y*z^4 + 2*x*y^4*z^2 + 4*x*y^3*z^3 + 2*x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * y^5 * (x - y)^2 + (4 : ℝ) * y^5 * (x - y)^1 * (z - x)^1 + (13 : ℝ) * y^5 * (z - x)^2 + (49 : ℝ) * y^4 * (x - y)^3 + (45 : ℝ) * y^4 * (x - y)^2 * (z - x)^1 + (40 : ℝ) * y^4 * (x - y)^1 * (z - x)^2 + (16 : ℝ) * y^4 * (z - x)^3 + (70 : ℝ) * y^3 * (x - y)^4 + (106 : ℝ) * y^3 * (x - y)^3 * (z - x)^1 + (70 : ℝ) * y^3 * (x - y)^2 * (z - x)^2 + (30 : ℝ) * y^3 * (x - y)^1 * (z - x)^3 + (4 : ℝ) * y^3 * (z - x)^4 + (46 : ℝ) * y^2 * (x - y)^5 + (96 : ℝ) * y^2 * (x - y)^4 * (z - x)^1 + (70 : ℝ) * y^2 * (x - y)^3 * (z - x)^2 + (24 : ℝ) * y^2 * (x - y)^2 * (z - x)^3 + (4 : ℝ) * y^2 * (x - y)^1 * (z - x)^4 + (13 : ℝ) * y^1 * (x - y)^6 + (34 : ℝ) * y^1 * (x - y)^5 * (z - x)^1 + (30 : ℝ) * y^1 * (x - y)^4 * (z - x)^2 + (10 : ℝ) * y^1 * (x - y)^3 * (z - x)^3 + (1 : ℝ) * y^1 * (x - y)^2 * (z - x)^4 + (1 : ℝ) * (x - y)^7 + (3 : ℝ) * (x - y)^6 * (z - x)^1 + (3 : ℝ) * (x - y)^5 * (z - x)^2 + (1 : ℝ) * (x - y)^4 * (z - x)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (x^4*y^3 + 3*x^4*y^2*z + 3*x^4*y*z^2 + x^4*z^3 + 2*x^3*y^3*z - 8*x^3*y^2*z^2 + 2*x^3*y*z^3 + x^2*y^4*z - 8*x^2*y^3*z^2 - 8*x^2*y^2*z^3 + x^2*y*z^4 + 2*x*y^4*z^2 + 4*x*y^3*z^3 + 2*x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * y^5 * (z - y)^2 + (22 : ℝ) * y^5 * (z - y)^1 * (x - z)^1 + (22 : ℝ) * y^5 * (x - z)^2 + (49 : ℝ) * y^4 * (z - y)^3 + (102 : ℝ) * y^4 * (z - y)^2 * (x - z)^1 + (97 : ℝ) * y^4 * (z - y)^1 * (x - z)^2 + (28 : ℝ) * y^4 * (x - z)^3 + (70 : ℝ) * y^3 * (z - y)^4 + (174 : ℝ) * y^3 * (z - y)^3 * (x - z)^1 + (172 : ℝ) * y^3 * (z - y)^2 * (x - z)^2 + (72 : ℝ) * y^3 * (z - y)^1 * (x - z)^3 + (8 : ℝ) * y^3 * (x - z)^4 + (46 : ℝ) * y^2 * (z - y)^5 + (134 : ℝ) * y^2 * (z - y)^4 * (x - z)^1 + (146 : ℝ) * y^2 * (z - y)^3 * (x - z)^2 + (70 : ℝ) * y^2 * (z - y)^2 * (x - z)^3 + (12 : ℝ) * y^2 * (z - y)^1 * (x - z)^4 + (13 : ℝ) * y^1 * (z - y)^6 + (44 : ℝ) * y^1 * (z - y)^5 * (x - z)^1 + (55 : ℝ) * y^1 * (z - y)^4 * (x - z)^2 + (30 : ℝ) * y^1 * (z - y)^3 * (x - z)^3 + (6 : ℝ) * y^1 * (z - y)^2 * (x - z)^4 + (1 : ℝ) * (z - y)^7 + (4 : ℝ) * (z - y)^6 * (x - z)^1 + (6 : ℝ) * (z - y)^5 * (x - z)^2 + (4 : ℝ) * (z - y)^4 * (x - z)^3 + (1 : ℝ) * (z - y)^3 * (x - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y^3 + 3*x^4*y^2*z + 3*x^4*y*z^2 + x^4*z^3 + 2*x^3*y^3*z - 8*x^3*y^2*z^2 + 2*x^3*y*z^3 + x^2*y^4*z - 8*x^2*y^3*z^2 - 8*x^2*y^2*z^3 + x^2*y*z^4 + 2*x*y^4*z^2 + 4*x*y^3*z^3 + 2*x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
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
  have hn : 0 ≤ (x^4*y^3 + 3*x^4*y^2*z + 3*x^4*y*z^2 + x^4*z^3 + 2*x^3*y^3*z - 8*x^3*y^2*z^2 + 2*x^3*y*z^3 + x^2*y^4*z - 8*x^2*y^3*z^2 - 8*x^2*y^2*z^3 + x^2*y*z^4 + 2*x*y^4*z^2 + 4*x*y^3*z^3 + 2*x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) / (x + y + z) * (1 / x + 1 / y + 1 / z) ^ 2 ≥ 12 / (x ^ 2 + y * z)) := @solution
#print axioms solution
