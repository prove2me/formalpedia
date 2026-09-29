-- Prove2me | solution 1 for WorkbookSource.base_7909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:34:43.476195+00:00
-- url     : https://prove2.me/submissions/1e414884-945d-4df2-a7bc-92b233b6c14d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x + z + y) * (2 * z + y + x) / (2 * y + x + z) + 2 * z * y * x / (x + y) / (y + z) ≥ 9 * z * x / (z + x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^4*y + 2*x^4*z + 5*x^3*y^2 + 5*x^3*y*z - 2*x^3*z^2 + 4*x^2*y^3 - 6*x^2*y^2*z - 12*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 10*x*y^3*z - 6*x*y^2*z^2 + 5*x*y*z^3 + 2*x*z^4 + y^4*z + 4*y^3*z^2 + 5*y^2*z^3 + 2*y*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * x^3 * (y - x)^2 + (60 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (32 : ℝ) * x^3 * (z - y)^2 + (72 : ℝ) * x^2 * (y - x)^3 + (159 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (117 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (24 : ℝ) * x^2 * (z - y)^3 + (52 : ℝ) * x^1 * (y - x)^4 + (129 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (114 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (39 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^1 * (z - y)^4 + (12 : ℝ) * (y - x)^5 + (32 : ℝ) * (y - x)^4 * (z - y)^1 + (31 : ℝ) * (y - x)^3 * (z - y)^2 + (13 : ℝ) * (y - x)^2 * (z - y)^3 + (2 : ℝ) * (y - x)^1 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (2*x^4*y + 2*x^4*z + 5*x^3*y^2 + 5*x^3*y*z - 2*x^3*z^2 + 4*x^2*y^3 - 6*x^2*y^2*z - 12*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 10*x*y^3*z - 6*x*y^2*z^2 + 5*x*y*z^3 + 2*x*z^4 + y^4*z + 4*y^3*z^2 + 5*y^2*z^3 + 2*y*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * x^3 * (z - x)^2 + (4 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (4 : ℝ) * x^3 * (y - z)^2 + (72 : ℝ) * x^2 * (z - x)^3 + (57 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (15 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (6 : ℝ) * x^2 * (y - z)^3 + (52 : ℝ) * x^1 * (z - x)^4 + (79 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (39 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (10 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (2 : ℝ) * x^1 * (y - z)^4 + (12 : ℝ) * (z - x)^5 + (28 : ℝ) * (z - x)^4 * (y - z)^1 + (23 : ℝ) * (z - x)^3 * (y - z)^2 + (8 : ℝ) * (z - x)^2 * (y - z)^3 + (1 : ℝ) * (z - x)^1 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (2*x^4*y + 2*x^4*z + 5*x^3*y^2 + 5*x^3*y*z - 2*x^3*z^2 + 4*x^2*y^3 - 6*x^2*y^2*z - 12*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 10*x*y^3*z - 6*x*y^2*z^2 + 5*x*y*z^3 + 2*x*z^4 + y^4*z + 4*y^3*z^2 + 5*y^2*z^3 + 2*y*z^4) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * y^3 * (x - y)^2 + (4 : ℝ) * y^3 * (x - y)^1 * (z - x)^1 + (32 : ℝ) * y^3 * (z - x)^2 + (6 : ℝ) * y^2 * (x - y)^3 + (9 : ℝ) * y^2 * (x - y)^2 * (z - x)^1 + (51 : ℝ) * y^2 * (x - y)^1 * (z - x)^2 + (24 : ℝ) * y^2 * (z - x)^3 + (2 : ℝ) * y^1 * (x - y)^4 + (4 : ℝ) * y^1 * (x - y)^3 * (z - x)^1 + (27 : ℝ) * y^1 * (x - y)^2 * (z - x)^2 + (25 : ℝ) * y^1 * (x - y)^1 * (z - x)^3 + (4 : ℝ) * y^1 * (z - x)^4 + (4 : ℝ) * (x - y)^3 * (z - x)^2 + (6 : ℝ) * (x - y)^2 * (z - x)^3 + (2 : ℝ) * (x - y)^1 * (z - x)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^4*y + 2*x^4*z + 5*x^3*y^2 + 5*x^3*y*z - 2*x^3*z^2 + 4*x^2*y^3 - 6*x^2*y^2*z - 12*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 10*x*y^3*z - 6*x*y^2*z^2 + 5*x*y*z^3 + 2*x*z^4 + y^4*z + 4*y^3*z^2 + 5*y^2*z^3 + 2*y*z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux2 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux2 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (2*x^4*y + 2*x^4*z + 5*x^3*y^2 + 5*x^3*y*z - 2*x^3*z^2 + 4*x^2*y^3 - 6*x^2*y^2*z - 12*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 10*x*y^3*z - 6*x*y^2*z^2 + 5*x*y*z^3 + 2*x*z^4 + y^4*z + 4*y^3*z^2 + 5*y^2*z^3 + 2*y*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 * x + z + y) * (2 * z + y + x) / (2 * y + x + z) + 2 * z * y * x / (x + y) / (y + z) ≥ 9 * z * x / (z + x)) := @solution
#print axioms solution
