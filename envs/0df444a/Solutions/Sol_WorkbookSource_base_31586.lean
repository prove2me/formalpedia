-- Prove2me | solution 1 for WorkbookSource.base_31586
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:26:59.126165+00:00
-- url     : https://prove2.me/submissions/7e07a0cd-1441-487e-a6eb-3bf31f5412db

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y / (z + x)) * (x + y) + (y / (z + x)) * (y + z) + x + (z / (x + y)) * (y + z) + (z / (x + y)) * (z + x) ≥ (5 / 2) * z + (5 / 2) * y  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^3 - x^2*y - x^2*z + x*y^2 - 4*x*y*z + x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^1 * (y - x)^2 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (10 : ℝ) * x^1 * (z - y)^2 + (2 : ℝ) * (y - x)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^1 + (9 : ℝ) * (y - x)^1 * (z - y)^2 + (4 : ℝ) * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (2*x^3 - x^2*y - x^2*z + x*y^2 - 4*x*y*z + x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * y^1 * (x - y)^2 + (16 : ℝ) * y^1 * (x - y)^1 * (z - x)^1 + (10 : ℝ) * y^1 * (z - x)^2 + (6 : ℝ) * (x - y)^3 + (13 : ℝ) * (x - y)^2 * (z - x)^1 + (13 : ℝ) * (x - y)^1 * (z - x)^2 + (4 : ℝ) * (z - x)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (2*x^3 - x^2*y - x^2*z + x*y^2 - 4*x*y*z + x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * y^1 * (z - y)^2 + (4 : ℝ) * y^1 * (z - y)^1 * (x - z)^1 + (4 : ℝ) * y^1 * (x - z)^2 + (6 : ℝ) * (z - y)^3 + (5 : ℝ) * (z - y)^2 * (x - z)^1 + (5 : ℝ) * (z - y)^1 * (x - z)^2 + (2 : ℝ) * (x - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^3 - x^2*y - x^2*z + x*y^2 - 4*x*y*z + x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by
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
  have hn : 0 ≤ (2*x^3 - x^2*y - x^2*z + x*y^2 - 4*x*y*z + x*z^2 + 4*y^3 - 3*y^2*z - 3*y*z^2 + 4*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y / (z + x)) * (x + y) + (y / (z + x)) * (y + z) + x + (z / (x + y)) * (y + z) + (z / (x + y)) * (z + x) ≥ (5 / 2) * z + (5 / 2) * y) := @solution
#print axioms solution
