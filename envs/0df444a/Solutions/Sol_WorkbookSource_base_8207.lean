-- Prove2me | solution 1 for WorkbookSource.base_8207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:34.362981+00:00
-- url     : https://prove2.me/submissions/0da65a78-187b-41df-b250-2b1c598ce661

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : 4 * x ^ 3 + (-4 * z - 4 * y) * x ^ 2 + (6 * y * z - z ^ 2 - y ^ 2) * x + 3 * (y + z) * (y - z) ^ 2 ≥ 0  := by
  have hp : 0 ≤ (4*x^3 - 4*x^2*y - 4*x^2*z - x*y^2 + 6*x*y*z - x*z^2 + 3*y^3 - 3*y^2*z - 3*y*z^2 + 3*z^3) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * x^1 * (y - x)^2 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (5 : ℝ) * x^1 * (z - y)^2 + (6 : ℝ) * (y - x)^1 * (z - y)^2 + (3 : ℝ) * (z - y)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * x^1 * (z - x)^2 + (4 : ℝ) * x^1 * (z - x)^1 * (y - z)^1 + (5 : ℝ) * x^1 * (y - z)^2 + (6 : ℝ) * (z - x)^1 * (y - z)^2 + (3 : ℝ) * (y - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * z^1 * (x - z)^2 + (6 : ℝ) * z^1 * (x - z)^1 * (y - x)^1 + (5 : ℝ) * z^1 * (y - x)^2 + (2 : ℝ) * (x - z)^3 + (3 : ℝ) * (x - z)^2 * (y - x)^1 + (8 : ℝ) * (x - z)^1 * (y - x)^2 + (3 : ℝ) * (y - x)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * y^1 * (x - y)^2 + (6 : ℝ) * y^1 * (x - y)^1 * (z - x)^1 + (5 : ℝ) * y^1 * (z - x)^2 + (2 : ℝ) * (x - y)^3 + (3 : ℝ) * (x - y)^2 * (z - x)^1 + (8 : ℝ) * (x - y)^1 * (z - x)^2 + (3 : ℝ) * (z - x)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * y^1 * (z - y)^2 + (4 : ℝ) * y^1 * (z - y)^1 * (x - z)^1 + (4 : ℝ) * y^1 * (x - z)^2 + (2 : ℝ) * (z - y)^3 + (3 : ℝ) * (z - y)^2 * (x - z)^1 + (8 : ℝ) * (z - y)^1 * (x - z)^2 + (4 : ℝ) * (x - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * z^1 * (y - z)^2 + (4 : ℝ) * z^1 * (y - z)^1 * (x - y)^1 + (4 : ℝ) * z^1 * (x - y)^2 + (2 : ℝ) * (y - z)^3 + (3 : ℝ) * (y - z)^2 * (x - y)^1 + (8 : ℝ) * (y - z)^1 * (x - y)^2 + (4 : ℝ) * (x - y)^3 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), 4 * x ^ 3 + (-4 * z - 4 * y) * x ^ 2 + (6 * y * z - z ^ 2 - y ^ 2) * x + 3 * (y + z) * (y - z) ^ 2 ≥ 0) := @solution
#print axioms solution
