-- Prove2me | solution 1 for WorkbookSource.base_14266
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:55:08.624848+00:00
-- url     : https://prove2.me/submissions/9d503df2-53c0-49b7-a7e3-180b03fa9800

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a + 2 * a * b / (a ^ 2 + b ^ 2) ≥ 4  := by
  have hp : 0 ≤ (a^4*c + a^3*b^2 - 4*a^3*b*c + 3*a^2*b^2*c + a^2*b*c^2 + a*b^4 - 4*a*b^3*c + b^3*c^2) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (1 : ℝ) * a^3 * (b - a)^2 + (2 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^3 * (c - b)^2 + (2 : ℝ) * a^2 * (b - a)^3 + (5 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (4 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (2 : ℝ) * a^1 * (b - a)^4 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (1 : ℝ) * (b - a)^5 + (2 : ℝ) * (b - a)^4 * (c - b)^1 + (1 : ℝ) * (b - a)^3 * (c - b)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (1 : ℝ) * a^3 * (c - a)^2 + (1 : ℝ) * a^3 * (b - c)^2 + (2 : ℝ) * a^2 * (c - a)^3 + (1 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (1 : ℝ) * a^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^4 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (3 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (1 : ℝ) * (c - a)^5 + (3 : ℝ) * (c - a)^4 * (b - c)^1 + (3 : ℝ) * (c - a)^3 * (b - c)^2 + (1 : ℝ) * (c - a)^2 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * c^3 * (a - c)^2 + (2 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (1 : ℝ) * c^3 * (b - a)^2 + (6 : ℝ) * c^2 * (a - c)^3 + (10 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (6 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (1 : ℝ) * c^2 * (b - a)^3 + (6 : ℝ) * c^1 * (a - c)^4 + (14 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (12 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (4 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (1 : ℝ) * c^1 * (b - a)^4 + (2 : ℝ) * (a - c)^5 + (6 : ℝ) * (a - c)^4 * (b - a)^1 + (7 : ℝ) * (a - c)^3 * (b - a)^2 + (4 : ℝ) * (a - c)^2 * (b - a)^3 + (1 : ℝ) * (a - c)^1 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (1 : ℝ) * b^3 * (a - b)^2 + (2 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (2 : ℝ) * b^3 * (c - a)^2 + (2 : ℝ) * b^2 * (a - b)^3 + (3 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (2 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (2 : ℝ) * b^1 * (a - b)^4 + (2 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (1 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (1 : ℝ) * (a - b)^5 + (1 : ℝ) * (a - b)^4 * (c - a)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (1 : ℝ) * b^3 * (c - b)^2 + (1 : ℝ) * b^3 * (a - c)^2 + (2 : ℝ) * b^2 * (c - b)^3 + (3 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (2 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (1 : ℝ) * b^2 * (a - c)^3 + (2 : ℝ) * b^1 * (c - b)^4 + (6 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (7 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (4 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (1 : ℝ) * b^1 * (a - c)^4 + (1 : ℝ) * (c - b)^5 + (4 : ℝ) * (c - b)^4 * (a - c)^1 + (6 : ℝ) * (c - b)^3 * (a - c)^2 + (4 : ℝ) * (c - b)^2 * (a - c)^3 + (1 : ℝ) * (c - b)^1 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * c^3 * (b - c)^2 + (2 : ℝ) * c^3 * (b - c)^1 * (a - b)^1 + (1 : ℝ) * c^3 * (a - b)^2 + (6 : ℝ) * c^2 * (b - c)^3 + (8 : ℝ) * c^2 * (b - c)^2 * (a - b)^1 + (4 : ℝ) * c^2 * (b - c)^1 * (a - b)^2 + (1 : ℝ) * c^2 * (a - b)^3 + (6 : ℝ) * c^1 * (b - c)^4 + (10 : ℝ) * c^1 * (b - c)^3 * (a - b)^1 + (6 : ℝ) * c^1 * (b - c)^2 * (a - b)^2 + (2 : ℝ) * c^1 * (b - c)^1 * (a - b)^3 + (1 : ℝ) * c^1 * (a - b)^4 + (2 : ℝ) * (b - c)^5 + (4 : ℝ) * (b - c)^4 * (a - b)^1 + (3 : ℝ) * (b - c)^3 * (a - b)^2 + (1 : ℝ) * (b - c)^2 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (a^4*c + a^3*b^2 - 4*a^3*b*c + 3*a^2*b^2*c + a^2*b*c^2 + a*b^4 - 4*a*b^3*c + b^3*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / b + b / c + c / a + 2 * a * b / (a ^ 2 + b ^ 2) ≥ 4) := @solution
#print axioms solution
