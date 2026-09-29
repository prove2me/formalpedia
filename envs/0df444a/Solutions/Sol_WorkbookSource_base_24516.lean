-- Prove2me | solution 1 for WorkbookSource.base_24516
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:30.103144+00:00
-- url     : https://prove2.me/submissions/9a04f88c-f9c4-4546-8980-9efc66d611dd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 1) : (x + 1) * (y + 2) * (z + 3) ≤ 12  := by
  have hp : 0 ≤ (2*x^2*z + 3*x*y^2 + 7*x*y*z + 6*x*z^2 + 3*y^3 + 9*y^2*z + 10*y*z^2 + 4*z^3) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (44 : ℝ) * x^3 + (112 : ℝ) * x^2 * (y - x)^1 + (62 : ℝ) * x^2 * (z - y)^1 + (94 : ℝ) * x^1 * (y - x)^2 + (101 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (28 : ℝ) * x^1 * (z - y)^2 + (26 : ℝ) * (y - x)^3 + (41 : ℝ) * (y - x)^2 * (z - y)^1 + (22 : ℝ) * (y - x)^1 * (z - y)^2 + (4 : ℝ) * (z - y)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (44 : ℝ) * x^3 + (112 : ℝ) * x^2 * (z - x)^1 + (50 : ℝ) * x^2 * (y - z)^1 + (94 : ℝ) * x^1 * (z - x)^2 + (87 : ℝ) * x^1 * (z - x)^1 * (y - z)^1 + (21 : ℝ) * x^1 * (y - z)^2 + (26 : ℝ) * (z - x)^3 + (37 : ℝ) * (z - x)^2 * (y - z)^1 + (18 : ℝ) * (z - x)^1 * (y - z)^2 + (3 : ℝ) * (y - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (44 : ℝ) * z^3 + (70 : ℝ) * z^2 * (x - z)^1 + (50 : ℝ) * z^2 * (y - x)^1 + (36 : ℝ) * z^1 * (x - z)^2 + (55 : ℝ) * z^1 * (x - z)^1 * (y - x)^1 + (21 : ℝ) * z^1 * (y - x)^2 + (6 : ℝ) * (x - z)^3 + (15 : ℝ) * (x - z)^2 * (y - x)^1 + (12 : ℝ) * (x - z)^1 * (y - x)^2 + (3 : ℝ) * (y - x)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (44 : ℝ) * y^3 + (82 : ℝ) * y^2 * (x - y)^1 + (62 : ℝ) * y^2 * (z - x)^1 + (53 : ℝ) * y^1 * (x - y)^2 + (79 : ℝ) * y^1 * (x - y)^1 * (z - x)^1 + (28 : ℝ) * y^1 * (z - x)^2 + (12 : ℝ) * (x - y)^3 + (26 : ℝ) * (x - y)^2 * (z - x)^1 + (18 : ℝ) * (x - y)^1 * (z - x)^2 + (4 : ℝ) * (z - x)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (44 : ℝ) * y^3 + (82 : ℝ) * y^2 * (z - y)^1 + (20 : ℝ) * y^2 * (x - z)^1 + (53 : ℝ) * y^1 * (z - y)^2 + (27 : ℝ) * y^1 * (z - y)^1 * (x - z)^1 + (2 : ℝ) * y^1 * (x - z)^2 + (12 : ℝ) * (z - y)^3 + (10 : ℝ) * (z - y)^2 * (x - z)^1 + (2 : ℝ) * (z - y)^1 * (x - z)^2 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (44 : ℝ) * z^3 + (70 : ℝ) * z^2 * (y - z)^1 + (20 : ℝ) * z^2 * (x - y)^1 + (36 : ℝ) * z^1 * (y - z)^2 + (17 : ℝ) * z^1 * (y - z)^1 * (x - y)^1 + (2 : ℝ) * z^1 * (x - y)^2 + (6 : ℝ) * (y - z)^3 + (3 : ℝ) * (y - z)^2 * (x - y)^1 := by positivity
          convert hpos using 1 <;> ring
  have he : (-x*y*z - 3*x*y - 2*x*z - 6*x - y*z - 3*y - 2*z + 6) = (2*x^2*z + 3*x*y^2 + 7*x*y*z + 6*x*z^2 + 3*y^3 + 9*y^2*z + 10*y*z^2 + 4*z^3) := by
    linear_combination (-2*x*z - 3*y^2 - 6*y*z - 3*y - 4*z^2 - 4*z - 6) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 1), (x + 1) * (y + 2) * (z + 3) ≤ 12) := @solution
#print axioms solution
