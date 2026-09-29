-- Prove2me | solution 1 for WorkbookSource.base_41900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:48.983168+00:00
-- url     : https://prove2.me/submissions/4e1ade2d-0d7e-46e7-84a0-7427d62eb9fa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + 2 * (y + z) / (x + y)) ≥ 4  := by
  have hp : 0 ≤ (x^2*z + x*y^2 - 3*x*y*z + y^3 - 2*y^2*z + 2*y*z^2) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (1 : ℝ) * x^1 * (y - x)^2 + (1 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (2 : ℝ) * x^1 * (z - y)^2 + (1 : ℝ) * (y - x)^3 + (2 : ℝ) * (y - x)^2 * (z - y)^1 + (2 : ℝ) * (y - x)^1 * (z - y)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (1 : ℝ) * x^1 * (z - x)^2 + (1 : ℝ) * x^1 * (z - x)^1 * (y - z)^1 + (2 : ℝ) * x^1 * (y - z)^2 + (1 : ℝ) * (z - x)^3 + (1 : ℝ) * (z - x)^2 * (y - z)^1 + (1 : ℝ) * (z - x)^1 * (y - z)^2 + (1 : ℝ) * (y - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * z^1 * (x - z)^2 + (3 : ℝ) * z^1 * (x - z)^1 * (y - x)^1 + (2 : ℝ) * z^1 * (y - x)^2 + (2 : ℝ) * (x - z)^3 + (5 : ℝ) * (x - z)^2 * (y - x)^1 + (4 : ℝ) * (x - z)^1 * (y - x)^2 + (1 : ℝ) * (y - x)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (2 : ℝ) * y^1 * (x - y)^2 + (3 : ℝ) * y^1 * (x - y)^1 * (z - x)^1 + (2 : ℝ) * y^1 * (z - x)^2 + (1 : ℝ) * (x - y)^3 + (1 : ℝ) * (x - y)^2 * (z - x)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * y^1 * (z - y)^2 + (1 : ℝ) * y^1 * (z - y)^1 * (x - z)^1 + (1 : ℝ) * y^1 * (x - z)^2 + (1 : ℝ) * (z - y)^3 + (2 : ℝ) * (z - y)^2 * (x - z)^1 + (1 : ℝ) * (z - y)^1 * (x - z)^2 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * z^1 * (y - z)^2 + (1 : ℝ) * z^1 * (y - z)^1 * (x - y)^1 + (1 : ℝ) * z^1 * (x - y)^2 + (2 : ℝ) * (y - z)^3 + (1 : ℝ) * (y - z)^2 * (x - y)^1 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (x^2*z + x*y^2 - 3*x*y*z + y^3 - 2*y^2*z + 2*y*z^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / y + y / z + 2 * (y + z) / (x + y)) ≥ 4) := @solution
#print axioms solution
