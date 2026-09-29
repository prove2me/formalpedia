-- Prove2me | solution 1 for WorkbookSource.base_19539
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:43.830635+00:00
-- url     : https://prove2.me/submissions/2fc13541-fe36-4ccd-b287-e6fd7ce69cdf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : a^3 + 2*a^2*b + 3*a*b*c ≤ 8  := by
  have hp : 0 ≤ (a^2*b + 3*a^2*c + 3*a*b^2 + 3*a*b*c + 3*a*c^2 + b^3 + 3*b^2*c + 3*b*c^2 + c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (21 : ℝ) * a^3 + (46 : ℝ) * a^2 * (b - a)^1 + (24 : ℝ) * a^2 * (c - b)^1 + (33 : ℝ) * a^1 * (b - a)^2 + (33 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^1 * (c - b)^2 + (8 : ℝ) * (b - a)^3 + (12 : ℝ) * (b - a)^2 * (c - b)^1 + (6 : ℝ) * (b - a)^1 * (c - b)^2 + (1 : ℝ) * (c - b)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (21 : ℝ) * a^3 + (46 : ℝ) * a^2 * (c - a)^1 + (22 : ℝ) * a^2 * (b - c)^1 + (33 : ℝ) * a^1 * (c - a)^2 + (33 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (9 : ℝ) * a^1 * (b - c)^2 + (8 : ℝ) * (c - a)^3 + (12 : ℝ) * (c - a)^2 * (b - c)^1 + (6 : ℝ) * (c - a)^1 * (b - c)^2 + (1 : ℝ) * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (21 : ℝ) * c^3 + (39 : ℝ) * c^2 * (a - c)^1 + (22 : ℝ) * c^2 * (b - a)^1 + (24 : ℝ) * c^1 * (a - c)^2 + (29 : ℝ) * c^1 * (a - c)^1 * (b - a)^1 + (9 : ℝ) * c^1 * (b - a)^2 + (5 : ℝ) * (a - c)^3 + (10 : ℝ) * (a - c)^2 * (b - a)^1 + (6 : ℝ) * (a - c)^1 * (b - a)^2 + (1 : ℝ) * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (21 : ℝ) * b^3 + (41 : ℝ) * b^2 * (a - b)^1 + (24 : ℝ) * b^2 * (c - a)^1 + (28 : ℝ) * b^1 * (a - b)^2 + (33 : ℝ) * b^1 * (a - b)^1 * (c - a)^1 + (9 : ℝ) * b^1 * (c - a)^2 + (7 : ℝ) * (a - b)^3 + (12 : ℝ) * (a - b)^2 * (c - a)^1 + (6 : ℝ) * (a - b)^1 * (c - a)^2 + (1 : ℝ) * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (21 : ℝ) * b^3 + (41 : ℝ) * b^2 * (c - b)^1 + (17 : ℝ) * b^2 * (a - c)^1 + (28 : ℝ) * b^1 * (c - b)^2 + (23 : ℝ) * b^1 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^1 * (a - c)^2 + (7 : ℝ) * (c - b)^3 + (9 : ℝ) * (c - b)^2 * (a - c)^1 + (3 : ℝ) * (c - b)^1 * (a - c)^2 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (21 : ℝ) * c^3 + (39 : ℝ) * c^2 * (b - c)^1 + (17 : ℝ) * c^2 * (a - b)^1 + (24 : ℝ) * c^1 * (b - c)^2 + (19 : ℝ) * c^1 * (b - c)^1 * (a - b)^1 + (4 : ℝ) * c^1 * (a - b)^2 + (5 : ℝ) * (b - c)^3 + (5 : ℝ) * (b - c)^2 * (a - b)^1 + (1 : ℝ) * (b - c)^1 * (a - b)^2 := by positivity
          convert hpos using 1 <;> ring
  have he : (-a^3 - 2*a^2*b - 3*a*b*c + 8) = (a^2*b + 3*a^2*c + 3*a*b^2 + 3*a*b*c + 3*a*c^2 + b^3 + 3*b^2*c + 3*b*c^2 + c^3) := by
    linear_combination (-a^2 - 2*a*b - 2*a*c - 2*a - b^2 - 2*b*c - 2*b - c^2 - 2*c - 4) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2), a^3 + 2*a^2*b + 3*a*b*c ≤ 8) := @solution
#print axioms solution
