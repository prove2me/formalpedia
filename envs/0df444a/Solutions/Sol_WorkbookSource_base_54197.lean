-- Prove2me | solution 1 for WorkbookSource.base_54197
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:35.433418+00:00
-- url     : https://prove2.me/submissions/b4ead74e-4155-4c9d-8802-1b773978da9f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / z + y * z / x + z * x / y + 9 * (x * y * z * (x + y + z) ^ 2) / (x * y + y * z + z * x) ^ 2) ≥ 4 * (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y^4 - 2*x^4*y^3*z + 3*x^4*y^2*z^2 - 2*x^4*y*z^3 + x^4*z^4 - 2*x^3*y^4*z - 2*x^3*y*z^4 + 3*x^2*y^4*z^2 + 3*x^2*y^2*z^4 - 2*x*y^4*z^3 - 2*x*y^3*z^4 + y^4*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * x^4 * (y - x)^4 + (2 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (3 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (2 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^4 * (z - y)^4 + (4 : ℝ) * x^3 * (y - x)^5 + (10 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (12 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (8 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (2 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (6 : ℝ) * x^2 * (y - x)^6 + (18 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (21 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (12 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (3 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (4 : ℝ) * x^1 * (y - x)^7 + (14 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (18 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (10 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (2 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1 : ℝ) * (y - x)^8 + (4 : ℝ) * (y - x)^7 * (z - y)^1 + (6 : ℝ) * (y - x)^6 * (z - y)^2 + (4 : ℝ) * (y - x)^5 * (z - y)^3 + (1 : ℝ) * (y - x)^4 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y^4 - 2*x^4*y^3*z + 3*x^4*y^2*z^2 - 2*x^4*y*z^3 + x^4*z^4 - 2*x^3*y^4*z - 2*x^3*y*z^4 + 3*x^2*y^4*z^2 + 3*x^2*y^2*z^4 - 2*x*y^4*z^3 - 2*x*y^3*z^4 + y^4*z^4) := by
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
  have hn : 0 ≤ ((x^2*y^2 - x^2*y*z + x^2*z^2 - x*y^2*z - x*y*z^2 + y^2*z^2)^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y / z + y * z / x + z * x / y + 9 * (x * y * z * (x + y + z) ^ 2) / (x * y + y * z + z * x) ^ 2) ≥ 4 * (x + y + z)) := @solution
#print axioms solution
