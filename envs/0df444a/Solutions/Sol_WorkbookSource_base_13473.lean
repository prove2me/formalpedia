-- Prove2me | solution 1 for WorkbookSource.base_13473
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:20.283214+00:00
-- url     : https://prove2.me/submissions/91791228-63f4-4e6e-b007-a757bf84cb65

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^3 + b^3 + c^3) + 3 * a * b * c ≥ 3 * (a^2 * b + b^2 * c + c^2 * a)  := by
  have hp : 0 ≤ (2*a^3 - 3*a^2*b + 3*a*b*c - 3*a*c^2 + 2*b^3 - 3*b^2*c + 2*c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^1 * (b - a)^2 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^1 * (c - b)^2 + (1 : ℝ) * (b - a)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^1 + (6 : ℝ) * (b - a)^1 * (c - b)^2 + (2 : ℝ) * (c - b)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^1 * (c - a)^2 + (3 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^1 * (b - c)^2 + (1 : ℝ) * (c - a)^3 + (3 : ℝ) * (c - a)^1 * (b - c)^2 + (2 : ℝ) * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^1 * (a - c)^2 + (3 : ℝ) * c^1 * (a - c)^1 * (b - a)^1 + (3 : ℝ) * c^1 * (b - a)^2 + (1 : ℝ) * (a - c)^3 + (3 : ℝ) * (a - c)^2 * (b - a)^1 + (6 : ℝ) * (a - c)^1 * (b - a)^2 + (2 : ℝ) * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * b^1 * (a - b)^2 + (3 : ℝ) * b^1 * (a - b)^1 * (c - a)^1 + (3 : ℝ) * b^1 * (c - a)^2 + (1 : ℝ) * (a - b)^3 + (3 : ℝ) * (a - b)^1 * (c - a)^2 + (2 : ℝ) * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * b^1 * (c - b)^2 + (3 : ℝ) * b^1 * (c - b)^1 * (a - c)^1 + (3 : ℝ) * b^1 * (a - c)^2 + (1 : ℝ) * (c - b)^3 + (3 : ℝ) * (c - b)^2 * (a - c)^1 + (6 : ℝ) * (c - b)^1 * (a - c)^2 + (2 : ℝ) * (a - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^1 * (b - c)^2 + (3 : ℝ) * c^1 * (b - c)^1 * (a - b)^1 + (3 : ℝ) * c^1 * (a - b)^2 + (1 : ℝ) * (b - c)^3 + (3 : ℝ) * (b - c)^1 * (a - b)^2 + (2 : ℝ) * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 * (a^3 + b^3 + c^3) + 3 * a * b * c ≥ 3 * (a^2 * b + b^2 * c + c^2 * a)) := @solution
#print axioms solution
