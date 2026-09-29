-- Prove2me | solution 1 for WorkbookSource.plus_4154
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:16:04.827121+00:00
-- url     : https://prove2.me/submissions/a79c8af3-7514-42c8-ab26-fbffd5068e3a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 / 9) * (x * y / z + y * z / x + z * x / y) + (x * y * z) / (x * y + y * z + z * x) ≥ x + y + z   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 8*x^3*z^3 - x^2*y^3*z - 18*x^2*y^2*z^2 - x^2*y*z^3 - x*y^3*z^2 - x*y^2*z^3 + 8*y^3*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * x^4 * (y - x)^2 + (22 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (22 : ℝ) * x^4 * (z - y)^2 + (74 : ℝ) * x^3 * (y - x)^3 + (111 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (65 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^3 * (z - y)^3 + (90 : ℝ) * x^2 * (y - x)^4 + (180 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (111 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (21 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (46 : ℝ) * x^1 * (y - x)^5 + (115 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (92 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (23 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (8 : ℝ) * (y - x)^6 + (24 : ℝ) * (y - x)^5 * (z - y)^1 + (24 : ℝ) * (y - x)^4 * (z - y)^2 + (8 : ℝ) * (y - x)^3 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 8*x^3*z^3 - x^2*y^3*z - 18*x^2*y^2*z^2 - x^2*y*z^3 - x*y^3*z^2 - x*y^2*z^3 + 8*y^3*z^3) := by
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
  have hn : 0 ≤ (8*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 8*x^3*z^3 - x^2*y^3*z - 18*x^2*y^2*z^2 - x^2*y*z^3 - x*y^3*z^2 - x*y^2*z^3 + 8*y^3*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (8 / 9) * (x * y / z + y * z / x + z * x / y) + (x * y * z) / (x * y + y * z + z * x) ≥ x + y + z) := @solution
#print axioms solution
