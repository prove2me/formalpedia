-- Prove2me | solution 1 for WorkbookSource.base_13239
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:50:56.351698+00:00
-- url     : https://prove2.me/submissions/31cb04fe-4f6f-4170-b4d5-28fa9f08f5d7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * z + 1) / (x + y + 1) + (1 + 2 * x) / (y + z + 1) + (2 * y + 1) / (z + x + 1) ≥ 3  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^3 - x^2*y - x^2*z + 2*x^2 - x*y^2 - 2*x*y - x*z^2 - 2*x*z + 2*y^3 - y^2*z + 2*y^2 - y*z^2 - 2*y*z + 2*z^3 + 2*z^2) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^1 * (y - x)^2 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^1 * (z - y)^2 + (2 : ℝ) * (y - x)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^1 + (2 : ℝ) * (y - x)^2 + (5 : ℝ) * (y - x)^1 * (z - y)^2 + (2 : ℝ) * (y - x)^1 * (z - y)^1 + (2 : ℝ) * (z - y)^3 + (2 : ℝ) * (z - y)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^3 - x^2*y - x^2*z + 2*x^2 - x*y^2 - 2*x*y - x*z^2 - 2*x*z + 2*y^3 - y^2*z + 2*y^2 - y*z^2 - 2*y*z + 2*z^3 + 2*z^2) := by
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
  have hn : 0 ≤ (2*x^3 - x^2*y - x^2*z + 2*x^2 - x*y^2 - 2*x*y - x*z^2 - 2*x*z + 2*y^3 - y^2*z + 2*y^2 - y*z^2 - 2*y*z + 2*z^3 + 2*z^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 * z + 1) / (x + y + 1) + (1 + 2 * x) / (y + z + 1) + (2 * y + 1) / (z + x + 1) ≥ 3) := @solution
#print axioms solution
