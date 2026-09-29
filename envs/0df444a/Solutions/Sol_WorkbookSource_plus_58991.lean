-- Prove2me | solution 1 for WorkbookSource.plus_58991
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:27.65604+00:00
-- url     : https://prove2.me/submissions/de88ad78-0e73-4cc5-b0e6-1191ad80089d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) ≥ x * y * z * (1 - 8 * x * y * z / ((x + y) * (y + z) * (z + x))) + 4 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 / ((x + y) * (y + z) * (z + x))   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 9*x^3*y^2*z - 9*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 9*x^2*y^3*z + 30*x^2*y^2*z^2 - 9*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 9*x*y^3*z^2 - 9*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (y - x)^2 + (6 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (6 : ℝ) * x^4 * (z - y)^2 + (10 : ℝ) * x^3 * (y - x)^3 + (15 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (33 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^3 * (z - y)^3 + (4 : ℝ) * x^2 * (y - x)^4 + (8 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (45 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (41 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (10 : ℝ) * x^2 * (z - y)^4 + (22 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (33 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (15 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 9*x^3*y^2*z - 9*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 9*x^2*y^3*z + 30*x^2*y^2*z^2 - 9*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 9*x*y^3*z^2 - 9*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
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
  have hn : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 9*x^3*y^2*z - 9*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 9*x^2*y^3*z + 30*x^2*y^2*z^2 - 9*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 9*x*y^3*z^2 - 9*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) ≥ x * y * z * (1 - 8 * x * y * z / ((x + y) * (y + z) * (z + x))) + 4 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 / ((x + y) * (y + z) * (z + x))) := @solution
#print axioms solution
