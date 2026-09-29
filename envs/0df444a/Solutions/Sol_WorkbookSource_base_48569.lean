-- Prove2me | solution 1 for WorkbookSource.base_48569
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:09.373273+00:00
-- url     : https://prove2.me/submissions/5c8693f2-a9c3-4938-b50c-50e8eced6cfc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2) * (1/(y + z) + 1/(x + z) + 1/(x + y)) ≥ 3/2 * (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^4 + 3*x^3*y + 3*x^3*z - 2*x^2*y^2 - 6*x^2*y*z - 2*x^2*z^2 + 3*x*y^3 - 6*x*y^2*z - 6*x*y*z^2 + 3*x*z^3 + 2*y^4 + 3*y^3*z - 2*y^2*z^2 + 3*y*z^3 + 2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * x^2 * (y - x)^2 + (20 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (20 : ℝ) * x^2 * (z - y)^2 + (26 : ℝ) * x^1 * (y - x)^3 + (39 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (41 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^1 * (z - y)^3 + (8 : ℝ) * (y - x)^4 + (16 : ℝ) * (y - x)^3 * (z - y)^1 + (19 : ℝ) * (y - x)^2 * (z - y)^2 + (11 : ℝ) * (y - x)^1 * (z - y)^3 + (2 : ℝ) * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^4 + 3*x^3*y + 3*x^3*z - 2*x^2*y^2 - 6*x^2*y*z - 2*x^2*z^2 + 3*x*y^3 - 6*x*y^2*z - 6*x*y*z^2 + 3*x*z^3 + 2*y^4 + 3*y^3*z - 2*y^2*z^2 + 3*y*z^3 + 2*z^4) := by
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
  have hn : 0 ≤ (2*x^4 + 3*x^3*y + 3*x^3*z - 2*x^2*y^2 - 6*x^2*y*z - 2*x^2*z^2 + 3*x*y^3 - 6*x*y^2*z - 6*x*y*z^2 + 3*x*z^3 + 2*y^4 + 3*y^3*z - 2*y^2*z^2 + 3*y*z^3 + 2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 + y^2 + z^2) * (1/(y + z) + 1/(x + z) + 1/(x + y)) ≥ 3/2 * (x + y + z)) := @solution
#print axioms solution
