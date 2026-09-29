-- Prove2me | solution 1 for WorkbookSource.base_8251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:35.090975+00:00
-- url     : https://prove2.me/submissions/d8c4b7da-654d-44b5-afd0-7ed74a30d8a9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x + y + z = 1) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) : 21 * x * y * z + 1 ≥ 16 * (x * y + x * z + y * z)^2  := by
  have hp : 0 ≤ (x^4 + 4*x^3*y + 4*x^3*z - 10*x^2*y^2 + x^2*y*z - 10*x^2*z^2 + 4*x*y^3 + x*y^2*z + x*y*z^2 + 4*x*z^3 + y^4 + 4*y^3*z - 10*y^2*z^2 + 4*y*z^3 + z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (11 : ℝ) * x^2 * (y - x)^2 + (11 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (11 : ℝ) * x^2 * (z - y)^2 + (10 : ℝ) * x^1 * (y - x)^3 + (15 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (29 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (12 : ℝ) * x^1 * (z - y)^3 + (8 : ℝ) * (y - x)^2 * (z - y)^2 + (8 : ℝ) * (y - x)^1 * (z - y)^3 + (1 : ℝ) * (z - y)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (11 : ℝ) * x^2 * (z - x)^2 + (11 : ℝ) * x^2 * (z - x)^1 * (y - z)^1 + (11 : ℝ) * x^2 * (y - z)^2 + (10 : ℝ) * x^1 * (z - x)^3 + (15 : ℝ) * x^1 * (z - x)^2 * (y - z)^1 + (29 : ℝ) * x^1 * (z - x)^1 * (y - z)^2 + (12 : ℝ) * x^1 * (y - z)^3 + (8 : ℝ) * (z - x)^2 * (y - z)^2 + (8 : ℝ) * (z - x)^1 * (y - z)^3 + (1 : ℝ) * (y - z)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (11 : ℝ) * z^2 * (x - z)^2 + (11 : ℝ) * z^2 * (x - z)^1 * (y - x)^1 + (11 : ℝ) * z^2 * (y - x)^2 + (10 : ℝ) * z^1 * (x - z)^3 + (15 : ℝ) * z^1 * (x - z)^2 * (y - x)^1 + (29 : ℝ) * z^1 * (x - z)^1 * (y - x)^2 + (12 : ℝ) * z^1 * (y - x)^3 + (8 : ℝ) * (x - z)^2 * (y - x)^2 + (8 : ℝ) * (x - z)^1 * (y - x)^3 + (1 : ℝ) * (y - x)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (11 : ℝ) * y^2 * (x - y)^2 + (11 : ℝ) * y^2 * (x - y)^1 * (z - x)^1 + (11 : ℝ) * y^2 * (z - x)^2 + (10 : ℝ) * y^1 * (x - y)^3 + (15 : ℝ) * y^1 * (x - y)^2 * (z - x)^1 + (29 : ℝ) * y^1 * (x - y)^1 * (z - x)^2 + (12 : ℝ) * y^1 * (z - x)^3 + (8 : ℝ) * (x - y)^2 * (z - x)^2 + (8 : ℝ) * (x - y)^1 * (z - x)^3 + (1 : ℝ) * (z - x)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (11 : ℝ) * y^2 * (z - y)^2 + (11 : ℝ) * y^2 * (z - y)^1 * (x - z)^1 + (11 : ℝ) * y^2 * (x - z)^2 + (10 : ℝ) * y^1 * (z - y)^3 + (15 : ℝ) * y^1 * (z - y)^2 * (x - z)^1 + (29 : ℝ) * y^1 * (z - y)^1 * (x - z)^2 + (12 : ℝ) * y^1 * (x - z)^3 + (8 : ℝ) * (z - y)^2 * (x - z)^2 + (8 : ℝ) * (z - y)^1 * (x - z)^3 + (1 : ℝ) * (x - z)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (11 : ℝ) * z^2 * (y - z)^2 + (11 : ℝ) * z^2 * (y - z)^1 * (x - y)^1 + (11 : ℝ) * z^2 * (x - y)^2 + (10 : ℝ) * z^1 * (y - z)^3 + (15 : ℝ) * z^1 * (y - z)^2 * (x - y)^1 + (29 : ℝ) * z^1 * (y - z)^1 * (x - y)^2 + (12 : ℝ) * z^1 * (x - y)^3 + (8 : ℝ) * (y - z)^2 * (x - y)^2 + (8 : ℝ) * (y - z)^1 * (x - y)^3 + (1 : ℝ) * (x - y)^4 := by positivity
          convert hpos using 1 <;> ring
  have he : (-16*x^2*y^2 - 32*x^2*y*z - 16*x^2*z^2 - 32*x*y^2*z - 32*x*y*z^2 + 21*x*y*z - 16*y^2*z^2 + 1) = (x^4 + 4*x^3*y + 4*x^3*z - 10*x^2*y^2 + x^2*y*z - 10*x^2*z^2 + 4*x*y^3 + x*y^2*z + x*y*z^2 + 4*x*z^3 + y^4 + 4*y^3*z - 10*y^2*z^2 + 4*y*z^3 + z^4) := by
    linear_combination (-x^3 - 3*x^2*y - 3*x^2*z - x^2 - 3*x*y^2 - 27*x*y*z - 2*x*y - 3*x*z^2 - 2*x*z - x - y^3 - 3*y^2*z - y^2 - 3*y*z^2 - 2*y*z - y - z^3 - z^2 - z - 1) * hx
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : x + y + z = 1) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z), 21 * x * y * z + 1 ≥ 16 * (x * y + x * z + y * z)^2) := @solution
#print axioms solution
