-- Prove2me | solution 1 for WorkbookSource.plus_4054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:16:04.122079+00:00
-- url     : https://prove2.me/submissions/dd86d295-8d50-4b8e-b1a3-14ec0c8780d8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) ^ 2 * 1 / (y + z) ^ 2 + 1 / (y + z) ^ 2 * 1 / (z + x) ^ 2 + 1 / (z + x) ^ 2 * 1 / (x + y) ^ 2) ≤ 9 / (16 * x * y * z * (x + y + z))   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (9*x^4*y^2 - 14*x^4*y*z + 9*x^4*z^2 + 18*x^3*y^3 - 10*x^3*y^2*z - 10*x^3*y*z^2 + 18*x^3*z^3 + 9*x^2*y^4 - 10*x^2*y^3*z - 6*x^2*y^2*z^2 - 10*x^2*y*z^3 + 9*x^2*z^4 - 14*x*y^4*z - 10*x*y^3*z^2 - 10*x*y^2*z^3 - 14*x*y*z^4 + 9*y^4*z^2 + 18*y^3*z^3 + 9*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * x^4 * (y - x)^2 + (64 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (64 : ℝ) * x^4 * (z - y)^2 + (224 : ℝ) * x^3 * (y - x)^3 + (336 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (176 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (32 : ℝ) * x^3 * (z - y)^3 + (292 : ℝ) * x^2 * (y - x)^4 + (584 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (348 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (56 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^2 * (z - y)^4 + (168 : ℝ) * x^1 * (y - x)^5 + (420 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (344 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (96 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (36 : ℝ) * (y - x)^6 + (108 : ℝ) * (y - x)^5 * (z - y)^1 + (117 : ℝ) * (y - x)^4 * (z - y)^2 + (54 : ℝ) * (y - x)^3 * (z - y)^3 + (9 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*x^4*y^2 - 14*x^4*y*z + 9*x^4*z^2 + 18*x^3*y^3 - 10*x^3*y^2*z - 10*x^3*y*z^2 + 18*x^3*z^3 + 9*x^2*y^4 - 10*x^2*y^3*z - 6*x^2*y^2*z^2 - 10*x^2*y*z^3 + 9*x^2*z^4 - 14*x*y^4*z - 10*x*y^3*z^2 - 10*x*y^2*z^3 - 14*x*y*z^4 + 9*y^4*z^2 + 18*y^3*z^3 + 9*y^2*z^4) := by
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
  have hn : 0 ≤ (9*x^4*y^2 - 14*x^4*y*z + 9*x^4*z^2 + 18*x^3*y^3 - 10*x^3*y^2*z - 10*x^3*y*z^2 + 18*x^3*z^3 + 9*x^2*y^4 - 10*x^2*y^3*z - 6*x^2*y^2*z^2 - 10*x^2*y*z^3 + 9*x^2*z^4 - 14*x*y^4*z - 10*x*y^3*z^2 - 10*x*y^2*z^3 - 14*x*y*z^4 + 9*y^4*z^2 + 18*y^3*z^3 + 9*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (x + y) ^ 2 * 1 / (y + z) ^ 2 + 1 / (y + z) ^ 2 * 1 / (z + x) ^ 2 + 1 / (z + x) ^ 2 * 1 / (x + y) ^ 2) ≤ 9 / (16 * x * y * z * (x + y + z))) := @solution
#print axioms solution
