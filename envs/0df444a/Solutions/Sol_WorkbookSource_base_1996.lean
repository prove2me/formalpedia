-- Prove2me | solution 1 for WorkbookSource.base_1996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:57:09.209402+00:00
-- url     : https://prove2.me/submissions/5ae3d02f-25bc-4d4d-92d5-dcd5389025a4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) ≥ 10  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - 6*x^4*y^2 + 2*x^4*y*z - 6*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 6*x^2*y^4 + 6*x^2*y^3*z - 11*x^2*y^2*z^2 + 6*x^2*y*z^3 - 6*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + y^6 + 2*y^5*z - 6*y^4*z^2 + 6*y^3*z^3 - 6*y^2*z^4 + 2*y*z^5 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * x^6 + (112 : ℝ) * x^5 * (y - x)^1 + (56 : ℝ) * x^5 * (z - y)^1 + (196 : ℝ) * x^4 * (y - x)^2 + (196 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (56 : ℝ) * x^4 * (z - y)^2 + (180 : ℝ) * x^3 * (y - x)^3 + (270 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (178 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (44 : ℝ) * x^3 * (z - y)^3 + (89 : ℝ) * x^2 * (y - x)^4 + (178 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (205 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (116 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (25 : ℝ) * x^2 * (z - y)^4 + (20 : ℝ) * x^1 * (y - x)^5 + (50 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (100 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (100 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (50 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (10 : ℝ) * x^1 * (z - y)^5 + (11 : ℝ) * (y - x)^4 * (z - y)^2 + (22 : ℝ) * (y - x)^3 * (z - y)^3 + (19 : ℝ) * (y - x)^2 * (z - y)^4 + (8 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - 6*x^4*y^2 + 2*x^4*y*z - 6*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 6*x^2*y^4 + 6*x^2*y^3*z - 11*x^2*y^2*z^2 + 6*x^2*y*z^3 - 6*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + y^6 + 2*y^5*z - 6*y^4*z^2 + 6*y^3*z^3 - 6*y^2*z^4 + 2*y*z^5 + z^6) := by
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
  have hn : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - 6*x^4*y^2 + 2*x^4*y*z - 6*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 6*x^2*y^4 + 6*x^2*y^3*z - 11*x^2*y^2*z^2 + 6*x^2*y*z^3 - 6*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + y^6 + 2*y^5*z - 6*y^4*z^2 + 6*y^3*z^3 - 6*y^2*z^4 + 2*y*z^5 + z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x + y + z) ^ 2 * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) ≥ 10) := @solution
#print axioms solution
