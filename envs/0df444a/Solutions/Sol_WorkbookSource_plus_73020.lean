-- Prove2me | solution 1 for WorkbookSource.plus_73020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:45:28.438749+00:00
-- url     : https://prove2.me/submissions/a4bd9eb1-5b78-4626-92a9-2b485e74b7bf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 2 + a + c^2 ≥ b * c^2   := by
  have hp : 0 ≤ (5*a^3/27 + 4*a^2*b/9 + 4*a^2*c/9 + a*b^2/3 + 2*a*b*c/3 + 2*a*c^2/3 + 2*b^3/27 + 2*b^2*c/9 - 4*b*c^2/9 + 11*c^3/27) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^3 + (5 : ℝ) * a^2 * (b - a)^1 + (3 : ℝ) * a^2 * (c - b)^1 + (22/9 : ℝ) * a^1 * (b - a)^2 + (28/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (13/9 : ℝ) * a^1 * (c - b)^2 + (7/27 : ℝ) * (b - a)^3 + (5/9 : ℝ) * (b - a)^2 * (c - b)^1 + (7/9 : ℝ) * (b - a)^1 * (c - b)^2 + (11/27 : ℝ) * (c - b)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^3 + (5 : ℝ) * a^2 * (c - a)^1 + (2 : ℝ) * a^2 * (b - c)^1 + (22/9 : ℝ) * a^1 * (c - a)^2 + (16/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (7/9 : ℝ) * a^1 * (b - c)^2 + (7/27 : ℝ) * (c - a)^3 + (2/9 : ℝ) * (c - a)^2 * (b - c)^1 + (4/9 : ℝ) * (c - a)^1 * (b - c)^2 + (2/27 : ℝ) * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^3 + (6 : ℝ) * c^2 * (a - c)^1 + (2 : ℝ) * c^2 * (b - a)^1 + (40/9 : ℝ) * c^1 * (a - c)^2 + (34/9 : ℝ) * c^1 * (a - c)^1 * (b - a)^1 + (7/9 : ℝ) * c^1 * (b - a)^2 + (28/27 : ℝ) * (a - c)^3 + (4/3 : ℝ) * (a - c)^2 * (b - a)^1 + (5/9 : ℝ) * (a - c)^1 * (b - a)^2 + (2/27 : ℝ) * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * b^3 + (7 : ℝ) * b^2 * (a - b)^1 + (3 : ℝ) * b^2 * (c - a)^1 + (52/9 : ℝ) * b^1 * (a - b)^2 + (52/9 : ℝ) * b^1 * (a - b)^1 * (c - a)^1 + (13/9 : ℝ) * b^1 * (c - a)^2 + (46/27 : ℝ) * (a - b)^3 + (3 : ℝ) * (a - b)^2 * (c - a)^1 + (17/9 : ℝ) * (a - b)^1 * (c - a)^2 + (11/27 : ℝ) * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * b^3 + (7 : ℝ) * b^2 * (c - b)^1 + (4 : ℝ) * b^2 * (a - c)^1 + (52/9 : ℝ) * b^1 * (c - b)^2 + (52/9 : ℝ) * b^1 * (c - b)^1 * (a - c)^1 + (13/9 : ℝ) * b^1 * (a - c)^2 + (46/27 : ℝ) * (c - b)^3 + (19/9 : ℝ) * (c - b)^2 * (a - c)^1 + (1 : ℝ) * (c - b)^1 * (a - c)^2 + (5/27 : ℝ) * (a - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^3 + (6 : ℝ) * c^2 * (b - c)^1 + (4 : ℝ) * c^2 * (a - b)^1 + (40/9 : ℝ) * c^1 * (b - c)^2 + (46/9 : ℝ) * c^1 * (b - c)^1 * (a - b)^1 + (13/9 : ℝ) * c^1 * (a - b)^2 + (28/27 : ℝ) * (b - c)^3 + (16/9 : ℝ) * (b - c)^2 * (a - b)^1 + (1 : ℝ) * (b - c)^1 * (a - b)^2 + (5/27 : ℝ) * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have he : (a - b*c^2 + c^2 + 2) = (5*a^3/27 + 4*a^2*b/9 + 4*a^2*c/9 + a*b^2/3 + 2*a*b*c/3 + 2*a*c^2/3 + 2*b^3/27 + 2*b^2*c/9 - 4*b*c^2/9 + 11*c^3/27) := by
    linear_combination (-5*a^2/27 - 7*a*b/27 - 7*a*c/27 - 5*a/9 - 2*b^2/27 - 4*b*c/27 - 2*b/9 - 11*c^2/27 - 2*c/9 - 2/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), 2 + a + c^2 ≥ b * c^2) := @solution
#print axioms solution
