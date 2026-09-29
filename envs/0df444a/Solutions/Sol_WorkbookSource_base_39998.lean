-- Prove2me | solution 1 for WorkbookSource.base_39998
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:33.951137+00:00
-- url     : https://prove2.me/submissions/8df2eb62-20b4-4793-bcdc-3bf22c8561c8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x ^ 2 + 2 * y * z) + (x + y + z) ^ 2 / (y ^ 2 + 2 * x * z) + (x + y + z) ^ 2 / (z ^ 2 + 2 * x * y) ≥ 9  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5*y + 2*x^5*z + 5*x^4*y^2 - 24*x^4*y*z + 5*x^4*z^2 - 12*x^3*y^3 + 20*x^3*y^2*z + 20*x^3*y*z^2 - 12*x^3*z^3 + 5*x^2*y^4 + 20*x^2*y^3*z - 54*x^2*y^2*z^2 + 20*x^2*y*z^3 + 5*x^2*z^4 + 2*x*y^5 - 24*x*y^4*z + 20*x*y^3*z^2 + 20*x*y^2*z^3 - 24*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 5*y^4*z^2 - 12*y^3*z^3 + 5*y^2*z^4 + 2*y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^2 * (y - x)^4 + (12 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (18 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (12 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (6 : ℝ) * x^2 * (z - y)^4 + (8 : ℝ) * x^1 * (y - x)^5 + (20 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (32 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (28 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (16 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (4 : ℝ) * x^1 * (z - y)^5 + (2 : ℝ) * (y - x)^6 + (6 : ℝ) * (y - x)^5 * (z - y)^1 + (19 : ℝ) * (y - x)^4 * (z - y)^2 + (28 : ℝ) * (y - x)^3 * (z - y)^3 + (15 : ℝ) * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5*y + 2*x^5*z + 5*x^4*y^2 - 24*x^4*y*z + 5*x^4*z^2 - 12*x^3*y^3 + 20*x^3*y^2*z + 20*x^3*y*z^2 - 12*x^3*z^3 + 5*x^2*y^4 + 20*x^2*y^3*z - 54*x^2*y^2*z^2 + 20*x^2*y*z^3 + 5*x^2*z^4 + 2*x*y^5 - 24*x*y^4*z + 20*x*y^3*z^2 + 20*x*y^2*z^3 - 24*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 5*y^4*z^2 - 12*y^3*z^3 + 5*y^2*z^4 + 2*y*z^5) := by
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
  have hn : 0 ≤ (2*x^5*y + 2*x^5*z + 5*x^4*y^2 - 24*x^4*y*z + 5*x^4*z^2 - 12*x^3*y^3 + 20*x^3*y^2*z + 20*x^3*y*z^2 - 12*x^3*z^3 + 5*x^2*y^4 + 20*x^2*y^3*z - 54*x^2*y^2*z^2 + 20*x^2*y*z^3 + 5*x^2*z^4 + 2*x*y^5 - 24*x*y^4*z + 20*x*y^3*z^2 + 20*x*y^2*z^3 - 24*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 5*y^4*z^2 - 12*y^3*z^3 + 5*y^2*z^4 + 2*y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y + z) ^ 2 / (x ^ 2 + 2 * y * z) + (x + y + z) ^ 2 / (y ^ 2 + 2 * x * z) + (x + y + z) ^ 2 / (z ^ 2 + 2 * x * y) ≥ 9) := @solution
#print axioms solution
