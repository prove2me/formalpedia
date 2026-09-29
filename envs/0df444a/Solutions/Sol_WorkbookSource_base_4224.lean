-- Prove2me | solution 1 for WorkbookSource.base_4224
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:39.494964+00:00
-- url     : https://prove2.me/submissions/a60e6c2c-a830-4900-8eeb-9d4dd5870f43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + 2 * y / (z + x) + 2 * z / (x + y) + x / (x + y)) ≥ 5 / 2 + z / (z + x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^1 * (y - x)^2 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^1 * (z - y)^2 + (2 : ℝ) * (y - x)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^1 + (9 : ℝ) * (y - x)^1 * (z - y)^2 + (4 : ℝ) * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (2*x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * y^1 * (x - y)^2 + (12 : ℝ) * y^1 * (x - y)^1 * (z - x)^1 + (8 : ℝ) * y^1 * (z - x)^2 + (4 : ℝ) * (x - y)^3 + (9 : ℝ) * (x - y)^2 * (z - x)^1 + (11 : ℝ) * (x - y)^1 * (z - x)^2 + (4 : ℝ) * (z - x)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (2*x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * y^1 * (z - y)^2 + (4 : ℝ) * y^1 * (z - y)^1 * (x - z)^1 + (4 : ℝ) * y^1 * (x - z)^2 + (4 : ℝ) * (z - y)^3 + (3 : ℝ) * (z - y)^2 * (x - z)^1 + (5 : ℝ) * (z - y)^1 * (x - z)^2 + (2 : ℝ) * (x - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
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
  have hn : 0 ≤ (2*x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y + z) + 2 * y / (z + x) + 2 * z / (x + y) + x / (x + y)) ≥ 5 / 2 + z / (z + x)) := @solution
#print axioms solution
