-- Prove2me | solution 1 for WorkbookSource.base_37184
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:05.974984+00:00
-- url     : https://prove2.me/submissions/6d29bae0-08e2-4bd5-b1de-87812ed7eed0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + z / (x + y)) ≥ (z + x) / (2 * y + z + x) + 1 / 8 * (-2 * y + 7 * z + 7 * x) / (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^4 + 17*x^3*y + x^3*z + 5*x^2*y^2 - 17*x^2*y*z - 14*x^2*z^2 - 18*x*y^2*z - 17*x*y*z^2 + x*z^3 + 4*y^4 + 5*y^2*z^2 + 17*y*z^3 + 8*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (76 : ℝ) * x^2 * (y - x)^2 + (136 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (76 : ℝ) * x^2 * (z - y)^2 + (102 : ℝ) * x^1 * (y - x)^3 + (230 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (194 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (50 : ℝ) * x^1 * (z - y)^3 + (34 : ℝ) * (y - x)^4 + (93 : ℝ) * (y - x)^3 * (z - y)^1 + (104 : ℝ) * (y - x)^2 * (z - y)^2 + (49 : ℝ) * (y - x)^1 * (z - y)^3 + (8 : ℝ) * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (8*x^4 + 17*x^3*y + x^3*z + 5*x^2*y^2 - 17*x^2*y*z - 14*x^2*z^2 - 18*x*y^2*z - 17*x*y*z^2 + x*z^3 + 4*y^4 + 5*y^2*z^2 + 17*y*z^3 + 8*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (76 : ℝ) * x^2 * (z - x)^2 + (16 : ℝ) * x^2 * (z - x)^1 * (y - z)^1 + (16 : ℝ) * x^2 * (y - z)^2 + (102 : ℝ) * x^1 * (z - x)^3 + (76 : ℝ) * x^1 * (z - x)^2 * (y - z)^1 + (40 : ℝ) * x^1 * (z - x)^1 * (y - z)^2 + (16 : ℝ) * x^1 * (y - z)^3 + (34 : ℝ) * (z - x)^4 + (43 : ℝ) * (z - x)^3 * (y - z)^1 + (29 : ℝ) * (z - x)^2 * (y - z)^2 + (16 : ℝ) * (z - x)^1 * (y - z)^3 + (4 : ℝ) * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (8*x^4 + 17*x^3*y + x^3*z + 5*x^2*y^2 - 17*x^2*y*z - 14*x^2*z^2 - 18*x*y^2*z - 17*x*y*z^2 + x*z^3 + 4*y^4 + 5*y^2*z^2 + 17*y*z^3 + 8*z^4) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * y^2 * (x - y)^2 + (16 : ℝ) * y^2 * (x - y)^1 * (z - x)^1 + (76 : ℝ) * y^2 * (z - x)^2 + (16 : ℝ) * y^1 * (x - y)^3 + (24 : ℝ) * y^1 * (x - y)^2 * (z - x)^1 + (108 : ℝ) * y^1 * (x - y)^1 * (z - x)^2 + (50 : ℝ) * y^1 * (z - x)^3 + (4 : ℝ) * (x - y)^4 + (8 : ℝ) * (x - y)^3 * (z - x)^1 + (37 : ℝ) * (x - y)^2 * (z - x)^2 + (33 : ℝ) * (x - y)^1 * (z - x)^3 + (8 : ℝ) * (z - x)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^4 + 17*x^3*y + x^3*z + 5*x^2*y^2 - 17*x^2*y*z - 14*x^2*z^2 - 18*x*y^2*z - 17*x*y*z^2 + x*z^3 + 4*y^4 + 5*y^2*z^2 + 17*y*z^3 + 8*z^4) := by
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
  have hn : 0 ≤ (8*x^4 + 17*x^3*y + x^3*z + 5*x^2*y^2 - 17*x^2*y*z - 14*x^2*z^2 - 18*x*y^2*z - 17*x*y*z^2 + x*z^3 + 4*y^4 + 5*y^2*z^2 + 17*y*z^3 + 8*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y + z) + z / (x + y)) ≥ (z + x) / (2 * y + z + x) + 1 / 8 * (-2 * y + 7 * z + 7 * x) / (x + y + z)) := @solution
#print axioms solution
