-- Prove2me | solution 1 for WorkbookSource.base_6095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:31.670723+00:00
-- url     : https://prove2.me/submissions/42368920-feb6-4ced-a7e0-f1642fe003f4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^4 * b + b^4 * c + c^4 * a ≥ a * b * c * (a^2 + b^2 + c^2)  := by
  have hp : 0 ≤ (a^4*b - a^3*b*c - a*b^3*c - a*b*c^3 + a*c^4 + b^4*c) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^3 * (b - a)^2 + (3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^3 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^3 + (6 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^4 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (1 : ℝ) * (b - a)^5 + (1 : ℝ) * (b - a)^4 * (c - b)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^3 * (c - a)^2 + (3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^3 * (b - c)^2 + (6 : ℝ) * a^2 * (c - a)^3 + (12 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^2 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^4 + (12 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (7 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (1 : ℝ) * (c - a)^5 + (4 : ℝ) * (c - a)^4 * (b - c)^1 + (6 : ℝ) * (c - a)^3 * (b - c)^2 + (4 : ℝ) * (c - a)^2 * (b - c)^3 + (1 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^3 * (a - c)^2 + (3 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (3 : ℝ) * c^3 * (b - a)^2 + (6 : ℝ) * c^2 * (a - c)^3 + (6 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (6 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (3 : ℝ) * c^2 * (b - a)^3 + (4 : ℝ) * c^1 * (a - c)^4 + (4 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (3 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (3 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (1 : ℝ) * c^1 * (b - a)^4 + (1 : ℝ) * (a - c)^5 + (1 : ℝ) * (a - c)^4 * (b - a)^1 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * b^3 * (a - b)^2 + (3 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (3 : ℝ) * b^3 * (c - a)^2 + (6 : ℝ) * b^2 * (a - b)^3 + (12 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (12 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (3 : ℝ) * b^2 * (c - a)^3 + (4 : ℝ) * b^1 * (a - b)^4 + (12 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (15 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (7 : ℝ) * b^1 * (a - b)^1 * (c - a)^3 + (1 : ℝ) * b^1 * (c - a)^4 + (1 : ℝ) * (a - b)^5 + (4 : ℝ) * (a - b)^4 * (c - a)^1 + (6 : ℝ) * (a - b)^3 * (c - a)^2 + (4 : ℝ) * (a - b)^2 * (c - a)^3 + (1 : ℝ) * (a - b)^1 * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * b^3 * (c - b)^2 + (3 : ℝ) * b^3 * (c - b)^1 * (a - c)^1 + (3 : ℝ) * b^3 * (a - c)^2 + (6 : ℝ) * b^2 * (c - b)^3 + (6 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (6 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (3 : ℝ) * b^2 * (a - c)^3 + (4 : ℝ) * b^1 * (c - b)^4 + (4 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (3 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (3 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (1 : ℝ) * b^1 * (a - c)^4 + (1 : ℝ) * (c - b)^5 + (1 : ℝ) * (c - b)^4 * (a - c)^1 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^3 * (b - c)^2 + (3 : ℝ) * c^3 * (b - c)^1 * (a - b)^1 + (3 : ℝ) * c^3 * (a - b)^2 + (6 : ℝ) * c^2 * (b - c)^3 + (12 : ℝ) * c^2 * (b - c)^2 * (a - b)^1 + (12 : ℝ) * c^2 * (b - c)^1 * (a - b)^2 + (3 : ℝ) * c^2 * (a - b)^3 + (4 : ℝ) * c^1 * (b - c)^4 + (12 : ℝ) * c^1 * (b - c)^3 * (a - b)^1 + (15 : ℝ) * c^1 * (b - c)^2 * (a - b)^2 + (7 : ℝ) * c^1 * (b - c)^1 * (a - b)^3 + (1 : ℝ) * c^1 * (a - b)^4 + (1 : ℝ) * (b - c)^5 + (4 : ℝ) * (b - c)^4 * (a - b)^1 + (6 : ℝ) * (b - c)^3 * (a - b)^2 + (4 : ℝ) * (b - c)^2 * (a - b)^3 + (1 : ℝ) * (b - c)^1 * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), a^4 * b + b^4 * c + c^4 * a ≥ a * b * c * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
