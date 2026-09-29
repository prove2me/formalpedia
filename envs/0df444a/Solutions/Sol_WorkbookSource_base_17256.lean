-- Prove2me | solution 1 for WorkbookSource.base_17256
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:07:49.119203+00:00
-- url     : https://prove2.me/submissions/c3121256-341e-4a4f-ac86-b929fe843cc1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 + y + 3 * x) / (2 + x + 3 * y) + (2 + z + 3 * y) / (2 + y + 3 * z) + (2 + x + 3 * z) / (2 + z + 3 * x) ≥ 3  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (10*x^2*y + 6*x^2*z + 8*x^2 + 6*x*y^2 - 48*x*y*z - 8*x*y + 10*x*z^2 - 8*x*z + 10*y^2*z + 8*y^2 + 6*y*z^2 - 8*y*z + 8*z^2) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * x^1 * (y - x)^2 + (16 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (16 : ℝ) * x^1 * (z - y)^2 + (16 : ℝ) * (y - x)^3 + (22 : ℝ) * (y - x)^2 * (z - y)^1 + (8 : ℝ) * (y - x)^2 + (6 : ℝ) * (y - x)^1 * (z - y)^2 + (8 : ℝ) * (y - x)^1 * (z - y)^1 + (8 : ℝ) * (z - y)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (10*x^2*y + 6*x^2*z + 8*x^2 + 6*x*y^2 - 48*x*y*z - 8*x*y + 10*x*z^2 - 8*x*z + 10*y^2*z + 8*y^2 + 6*y*z^2 - 8*y*z + 8*z^2) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * x^1 * (z - x)^2 + (16 : ℝ) * x^1 * (z - x)^1 * (y - z)^1 + (16 : ℝ) * x^1 * (y - z)^2 + (16 : ℝ) * (z - x)^3 + (26 : ℝ) * (z - x)^2 * (y - z)^1 + (8 : ℝ) * (z - x)^2 + (10 : ℝ) * (z - x)^1 * (y - z)^2 + (8 : ℝ) * (z - x)^1 * (y - z)^1 + (8 : ℝ) * (y - z)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*x^2*y + 6*x^2*z + 8*x^2 + 6*x*y^2 - 48*x*y*z - 8*x*y + 10*x*z^2 - 8*x*z + 10*y^2*z + 8*y^2 + 6*y*z^2 - 8*y*z + 8*z^2) := by
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
  have hn : 0 ≤ (10*x^2*y + 6*x^2*z + 8*x^2 + 6*x*y^2 - 48*x*y*z - 8*x*y + 10*x*z^2 - 8*x*z + 10*y^2*z + 8*y^2 + 6*y*z^2 - 8*y*z + 8*z^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 + y + 3 * x) / (2 + x + 3 * y) + (2 + z + 3 * y) / (2 + y + 3 * z) + (2 + x + 3 * z) / (2 + z + 3 * x) ≥ 3) := @solution
#print axioms solution
