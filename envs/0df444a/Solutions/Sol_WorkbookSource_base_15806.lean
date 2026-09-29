-- Prove2me | solution 1 for WorkbookSource.base_15806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:06.69463+00:00
-- url     : https://prove2.me/submissions/0c280d4f-ce91-4940-a811-4e951bda1eca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 27 * ((x + y) * (y + z) * (z + x)) ^ 2 ≥ 64 * x * y * z * (x + y + z) ^ 3  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (27*x^4*y^2 - 10*x^4*y*z + 27*x^4*z^2 + 54*x^3*y^3 - 30*x^3*y^2*z - 30*x^3*y*z^2 + 54*x^3*z^3 + 27*x^2*y^4 - 30*x^2*y^3*z - 114*x^2*y^2*z^2 - 30*x^2*y*z^3 + 27*x^2*z^4 - 10*x*y^4*z - 30*x*y^3*z^2 - 30*x*y^2*z^3 - 10*x*y*z^4 + 27*y^4*z^2 + 54*y^3*z^3 + 27*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (288 : ℝ) * x^4 * (y - x)^2 + (288 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (288 : ℝ) * x^4 * (z - y)^2 + (928 : ℝ) * x^3 * (y - x)^3 + (1392 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (912 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (224 : ℝ) * x^3 * (z - y)^3 + (1100 : ℝ) * x^2 * (y - x)^4 + (2200 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1524 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (424 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (44 : ℝ) * x^2 * (z - y)^4 + (568 : ℝ) * x^1 * (y - x)^5 + (1420 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (1224 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (416 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (44 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (108 : ℝ) * (y - x)^6 + (324 : ℝ) * (y - x)^5 * (z - y)^1 + (351 : ℝ) * (y - x)^4 * (z - y)^2 + (162 : ℝ) * (y - x)^3 * (z - y)^3 + (27 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (27*x^4*y^2 - 10*x^4*y*z + 27*x^4*z^2 + 54*x^3*y^3 - 30*x^3*y^2*z - 30*x^3*y*z^2 + 54*x^3*z^3 + 27*x^2*y^4 - 30*x^2*y^3*z - 114*x^2*y^2*z^2 - 30*x^2*y*z^3 + 27*x^2*z^4 - 10*x*y^4*z - 30*x*y^3*z^2 - 30*x*y^2*z^3 - 10*x*y*z^4 + 27*y^4*z^2 + 54*y^3*z^3 + 27*y^2*z^4) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), 27 * ((x + y) * (y + z) * (z + x)) ^ 2 ≥ 64 * x * y * z * (x + y + z) ^ 3) := @solution
#print axioms solution
