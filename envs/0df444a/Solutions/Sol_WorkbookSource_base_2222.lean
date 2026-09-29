-- Prove2me | solution 1 for WorkbookSource.base_2222
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:21.85429+00:00
-- url     : https://prove2.me/submissions/06c44846-fe73-4977-b33e-2199cce80e4d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : c^3*a + a^4 + b^3*c ≥ a*c*(b*c + b^2 + a^2)  := by
  have hp : 0 ≤ (a^4 - a^3*c - a*b^2*c - a*b*c^2 + a*c^3 + b^3*c) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^2 * (b - a)^2 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^2 * (c - b)^2 + (3 : ℝ) * a^1 * (b - a)^3 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (1 : ℝ) * a^1 * (c - b)^3 + (1 : ℝ) * (b - a)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^2 * (c - a)^2 + (3 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^2 * (b - c)^2 + (3 : ℝ) * a^1 * (c - a)^3 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (1 : ℝ) * a^1 * (b - c)^3 + (1 : ℝ) * (c - a)^4 + (3 : ℝ) * (c - a)^3 * (b - c)^1 + (3 : ℝ) * (c - a)^2 * (b - c)^2 + (1 : ℝ) * (c - a)^1 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * c^2 * (a - c)^2 + (1 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (2 : ℝ) * c^2 * (b - a)^2 + (3 : ℝ) * c^1 * (a - c)^3 + (1 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (2 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (1 : ℝ) * c^1 * (b - a)^3 + (1 : ℝ) * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (2 : ℝ) * b^2 * (a - b)^2 + (1 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (2 : ℝ) * b^2 * (c - a)^2 + (3 : ℝ) * b^1 * (a - b)^3 + (4 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (5 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (1 : ℝ) * b^1 * (c - a)^3 + (1 : ℝ) * (a - b)^4 + (2 : ℝ) * (a - b)^3 * (c - a)^1 + (3 : ℝ) * (a - b)^2 * (c - a)^2 + (1 : ℝ) * (a - b)^1 * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * b^2 * (c - b)^2 + (3 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (3 : ℝ) * b^2 * (a - c)^2 + (3 : ℝ) * b^1 * (c - b)^3 + (5 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (6 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (3 : ℝ) * b^1 * (a - c)^3 + (1 : ℝ) * (c - b)^4 + (2 : ℝ) * (c - b)^3 * (a - c)^1 + (3 : ℝ) * (c - b)^2 * (a - c)^2 + (3 : ℝ) * (c - b)^1 * (a - c)^3 + (1 : ℝ) * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * c^2 * (b - c)^2 + (3 : ℝ) * c^2 * (b - c)^1 * (a - b)^1 + (3 : ℝ) * c^2 * (a - b)^2 + (3 : ℝ) * c^1 * (b - c)^3 + (8 : ℝ) * c^1 * (b - c)^2 * (a - b)^1 + (9 : ℝ) * c^1 * (b - c)^1 * (a - b)^2 + (3 : ℝ) * c^1 * (a - b)^3 + (1 : ℝ) * (b - c)^4 + (4 : ℝ) * (b - c)^3 * (a - b)^1 + (6 : ℝ) * (b - c)^2 * (a - b)^2 + (4 : ℝ) * (b - c)^1 * (a - b)^3 + (1 : ℝ) * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), c^3*a + a^4 + b^3*c ≥ a*c*(b*c + b^2 + a^2)) := @solution
#print axioms solution
