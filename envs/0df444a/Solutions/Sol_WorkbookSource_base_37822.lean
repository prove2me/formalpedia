-- Prove2me | solution 1 for WorkbookSource.base_37822
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:40.840092+00:00
-- url     : https://prove2.me/submissions/02103c9c-d4f9-49cc-b260-a90f35a0efc4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x + y + z) ≥ x / ((y + 2 * x) * (z + 2 * x)) + y / ((2 * y + z) * (2 * y + x)) + z / ((2 * z + x) * (2 * z + y))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^4*y^2 - x^4*y*z + 2*x^4*z^2 + 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 + 8*x^3*z^3 + 2*x^2*y^4 - 5*x^2*y^3*z - 3*x^2*y^2*z^2 - 5*x^2*y*z^3 + 2*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 - x*y*z^4 + 2*y^4*z^2 + 8*y^3*z^3 + 2*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * x^4 * (y - x)^2 + (27 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (27 : ℝ) * x^4 * (z - y)^2 + (90 : ℝ) * x^3 * (y - x)^3 + (135 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (81 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (18 : ℝ) * x^3 * (z - y)^3 + (111 : ℝ) * x^2 * (y - x)^4 + (222 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (144 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (33 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (3 : ℝ) * x^2 * (z - y)^4 + (60 : ℝ) * x^1 * (y - x)^5 + (150 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (126 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (39 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (3 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (12 : ℝ) * (y - x)^6 + (36 : ℝ) * (y - x)^5 * (z - y)^1 + (38 : ℝ) * (y - x)^4 * (z - y)^2 + (16 : ℝ) * (y - x)^3 * (z - y)^3 + (2 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^4*y^2 - x^4*y*z + 2*x^4*z^2 + 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 + 8*x^3*z^3 + 2*x^2*y^4 - 5*x^2*y^3*z - 3*x^2*y^2*z^2 - 5*x^2*y*z^3 + 2*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 - x*y*z^4 + 2*y^4*z^2 + 8*y^3*z^3 + 2*y^2*z^4) := by
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
  have hn : 0 ≤ (2*x^4*y^2 - x^4*y*z + 2*x^4*z^2 + 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 + 8*x^3*z^3 + 2*x^2*y^4 - 5*x^2*y^3*z - 3*x^2*y^2*z^2 - 5*x^2*y*z^3 + 2*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 - x*y*z^4 + 2*y^4*z^2 + 8*y^3*z^3 + 2*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 1 / (x + y + z) ≥ x / ((y + 2 * x) * (z + 2 * x)) + y / ((2 * y + z) * (2 * y + x)) + z / ((2 * z + x) * (2 * z + y))) := @solution
#print axioms solution
