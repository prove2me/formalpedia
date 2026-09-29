-- Prove2me | solution 1 for WorkbookSource.base_28399
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:49.378995+00:00
-- url     : https://prove2.me/submissions/d580f78c-e67e-44ee-982b-83196b3b864a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (y + z) ^ 2 + 1 / (z + x) ^ 2 + 1 / (x + y) ^ 2) ≥ (x + y + z) * (9 * (x + y) * (y + z) * (z + x) - 8 * x * y * z) / (4 * (x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^4 - x^3*y - x^3*z - 6*x^2*y^2 + 4*x^2*y*z - 6*x^2*z^2 - x*y^3 + 4*x*y^2*z + 4*x*y*z^2 - x*z^3 + 4*y^4 - y^3*z - 6*y^2*z^2 - y*z^3 + 4*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * x^2 * (y - x)^2 + (10 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (10 : ℝ) * x^2 * (z - y)^2 + (6 : ℝ) * x^1 * (y - x)^3 + (9 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (31 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^1 * (z - y)^3 + (15 : ℝ) * (y - x)^2 * (z - y)^2 + (15 : ℝ) * (y - x)^1 * (z - y)^3 + (4 : ℝ) * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^4 - x^3*y - x^3*z - 6*x^2*y^2 + 4*x^2*y*z - 6*x^2*z^2 - x*y^3 + 4*x*y^2*z + 4*x*y*z^2 - x*z^3 + 4*y^4 - y^3*z - 6*y^2*z^2 - y*z^3 + 4*z^4) := by
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
  have hn : 0 ≤ (4*x^4 - x^3*y - x^3*z - 6*x^2*y^2 + 4*x^2*y*z - 6*x^2*z^2 - x*y^3 + 4*x*y^2*z + 4*x*y*z^2 - x*z^3 + 4*y^4 - y^3*z - 6*y^2*z^2 - y*z^3 + 4*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (y + z) ^ 2 + 1 / (z + x) ^ 2 + 1 / (x + y) ^ 2) ≥ (x + y + z) * (9 * (x + y) * (y + z) * (z + x) - 8 * x * y * z) / (4 * (x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2)) := @solution
#print axioms solution
