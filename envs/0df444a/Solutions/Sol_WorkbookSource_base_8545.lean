-- Prove2me | solution 1 for WorkbookSource.base_8545
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:36.627909+00:00
-- url     : https://prove2.me/submissions/326e4723-3052-4358-b7ed-8f2847a3b86c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 + a * b * c * (a * b + b * c + c * a) ≥ a^3 * (b^2 + c^2) + b^3 * (c^2 + a^2) + c^3 * (a^2 + b^2)  := by
  have hp : 0 ≤ (a^5 - a^3*b^2 - a^3*c^2 - a^2*b^3 + a^2*b^2*c + a^2*b*c^2 - a^2*c^3 + a*b^2*c^2 + b^5 - b^3*c^2 - b^2*c^3 + c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * a^3 * (b - a)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^3 * (c - b)^2 + (4 : ℝ) * a^2 * (b - a)^3 + (6 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (18 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^2 * (c - b)^3 + (1 : ℝ) * a^1 * (b - a)^4 + (2 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (19 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (5 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^2 + (9 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * a^3 * (c - a)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^3 * (b - c)^2 + (4 : ℝ) * a^2 * (c - a)^3 + (6 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (18 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (8 : ℝ) * a^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^4 + (2 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (19 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (18 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (5 : ℝ) * a^1 * (b - c)^4 + (6 : ℝ) * (c - a)^3 * (b - c)^2 + (9 : ℝ) * (c - a)^2 * (b - c)^3 + (5 : ℝ) * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (b - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * c^3 * (a - c)^2 + (4 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (4 : ℝ) * c^3 * (b - a)^2 + (4 : ℝ) * c^2 * (a - c)^3 + (6 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (18 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (8 : ℝ) * c^2 * (b - a)^3 + (1 : ℝ) * c^1 * (a - c)^4 + (2 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (19 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (18 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (5 : ℝ) * c^1 * (b - a)^4 + (6 : ℝ) * (a - c)^3 * (b - a)^2 + (9 : ℝ) * (a - c)^2 * (b - a)^3 + (5 : ℝ) * (a - c)^1 * (b - a)^4 + (1 : ℝ) * (b - a)^5 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * b^3 * (a - b)^2 + (4 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (4 : ℝ) * b^3 * (c - a)^2 + (4 : ℝ) * b^2 * (a - b)^3 + (6 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (18 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (8 : ℝ) * b^2 * (c - a)^3 + (1 : ℝ) * b^1 * (a - b)^4 + (2 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (19 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (18 : ℝ) * b^1 * (a - b)^1 * (c - a)^3 + (5 : ℝ) * b^1 * (c - a)^4 + (6 : ℝ) * (a - b)^3 * (c - a)^2 + (9 : ℝ) * (a - b)^2 * (c - a)^3 + (5 : ℝ) * (a - b)^1 * (c - a)^4 + (1 : ℝ) * (c - a)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * b^3 * (c - b)^2 + (4 : ℝ) * b^3 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^3 * (a - c)^2 + (4 : ℝ) * b^2 * (c - b)^3 + (6 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (18 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (8 : ℝ) * b^2 * (a - c)^3 + (1 : ℝ) * b^1 * (c - b)^4 + (2 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (19 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (18 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (5 : ℝ) * b^1 * (a - c)^4 + (6 : ℝ) * (c - b)^3 * (a - c)^2 + (9 : ℝ) * (c - b)^2 * (a - c)^3 + (5 : ℝ) * (c - b)^1 * (a - c)^4 + (1 : ℝ) * (a - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * c^3 * (b - c)^2 + (4 : ℝ) * c^3 * (b - c)^1 * (a - b)^1 + (4 : ℝ) * c^3 * (a - b)^2 + (4 : ℝ) * c^2 * (b - c)^3 + (6 : ℝ) * c^2 * (b - c)^2 * (a - b)^1 + (18 : ℝ) * c^2 * (b - c)^1 * (a - b)^2 + (8 : ℝ) * c^2 * (a - b)^3 + (1 : ℝ) * c^1 * (b - c)^4 + (2 : ℝ) * c^1 * (b - c)^3 * (a - b)^1 + (19 : ℝ) * c^1 * (b - c)^2 * (a - b)^2 + (18 : ℝ) * c^1 * (b - c)^1 * (a - b)^3 + (5 : ℝ) * c^1 * (a - b)^4 + (6 : ℝ) * (b - c)^3 * (a - b)^2 + (9 : ℝ) * (b - c)^2 * (a - b)^3 + (5 : ℝ) * (b - c)^1 * (a - b)^4 + (1 : ℝ) * (a - b)^5 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^5 + b^5 + c^5 + a * b * c * (a * b + b * c + c * a) ≥ a^3 * (b^2 + c^2) + b^3 * (c^2 + a^2) + c^3 * (a^2 + b^2)) := @solution
#print axioms solution
