-- Prove2me | solution 1 for WorkbookSource.base_27490
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:04.569231+00:00
-- url     : https://prove2.me/submissions/fe739813-b963-4a9b-9b10-c930d639e34f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + c) + 6 * b / (c + a) + 3 * c / (a + b)) ≥ 4  := by
  have hp : 0 ≤ (2*a^3 - 2*a^2*b - 2*a^2*c + 2*a*b^2 + 3*a*b*c - a*c^2 + 6*b^3 + 2*b^2*c - b*c^2 + 3*c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * a^3 + (34 : ℝ) * a^2 * (b - a)^1 + (8 : ℝ) * a^2 * (c - b)^1 + (34 : ℝ) * a^1 * (b - a)^2 + (19 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (7 : ℝ) * a^1 * (c - b)^2 + (10 : ℝ) * (b - a)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^1 + (8 : ℝ) * (b - a)^1 * (c - b)^2 + (3 : ℝ) * (c - b)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * a^3 + (34 : ℝ) * a^2 * (c - a)^1 + (26 : ℝ) * a^2 * (b - c)^1 + (34 : ℝ) * a^1 * (c - a)^2 + (49 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (22 : ℝ) * a^1 * (b - c)^2 + (10 : ℝ) * (c - a)^3 + (21 : ℝ) * (c - a)^2 * (b - c)^1 + (20 : ℝ) * (c - a)^1 * (b - c)^2 + (6 : ℝ) * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^3 + (28 : ℝ) * c^2 * (a - c)^1 + (26 : ℝ) * c^2 * (b - a)^1 + (27 : ℝ) * c^1 * (a - c)^2 + (47 : ℝ) * c^1 * (a - c)^1 * (b - a)^1 + (22 : ℝ) * c^1 * (b - a)^2 + (8 : ℝ) * (a - c)^3 + (20 : ℝ) * (a - c)^2 * (b - a)^1 + (20 : ℝ) * (a - c)^1 * (b - a)^2 + (6 : ℝ) * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * b^3 + (10 : ℝ) * b^2 * (a - b)^1 + (8 : ℝ) * b^2 * (c - a)^1 + (6 : ℝ) * b^1 * (a - b)^2 + (11 : ℝ) * b^1 * (a - b)^1 * (c - a)^1 + (7 : ℝ) * b^1 * (c - a)^2 + (2 : ℝ) * (a - b)^3 + (5 : ℝ) * (a - b)^2 * (c - a)^1 + (8 : ℝ) * (a - b)^1 * (c - a)^2 + (3 : ℝ) * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * b^3 + (10 : ℝ) * b^2 * (c - b)^1 + (2 : ℝ) * b^2 * (a - c)^1 + (6 : ℝ) * b^1 * (c - b)^2 + (1 : ℝ) * b^1 * (c - b)^1 * (a - c)^1 + (2 : ℝ) * b^1 * (a - c)^2 + (2 : ℝ) * (c - b)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^1 + (4 : ℝ) * (c - b)^1 * (a - c)^2 + (2 : ℝ) * (a - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^3 + (28 : ℝ) * c^2 * (b - c)^1 + (2 : ℝ) * c^2 * (a - b)^1 + (27 : ℝ) * c^1 * (b - c)^2 + (7 : ℝ) * c^1 * (b - c)^1 * (a - b)^1 + (2 : ℝ) * c^1 * (a - b)^2 + (8 : ℝ) * (b - c)^3 + (4 : ℝ) * (b - c)^2 * (a - b)^1 + (4 : ℝ) * (b - c)^1 * (a - b)^2 + (2 : ℝ) * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (2*a^3 - 2*a^2*b - 2*a^2*c + 2*a*b^2 + 3*a*b*c - a*c^2 + 6*b^3 + 2*b^2*c - b*c^2 + 3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a / (b + c) + 6 * b / (c + a) + 3 * c / (a + b)) ≥ 4) := @solution
#print axioms solution
