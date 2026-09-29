-- Prove2me | solution 1 for WorkbookSource.base_21608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:12.319671+00:00
-- url     : https://prove2.me/submissions/ce4897fe-40c0-4e69-8669-9124e93e0573

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 1) ^ 2 ≥ (2 * a + b + c) * (2 / a + 1 / b + 1 / c)  := by
  have hp : 0 ≤ (a^4*c^2 + a^2*b^4 + a^2*b^3*c - 5*a^2*b^2*c^2 + a^2*b*c^3 + b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5 : ℝ) * a^4 * (c - b)^2 + (12 : ℝ) * a^3 * (b - a)^3 + (22 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (20 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^3 * (c - b)^3 + (13 : ℝ) * a^2 * (b - a)^4 + (34 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (34 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (13 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (24 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (12 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (b - a)^6 + (4 : ℝ) * (b - a)^5 * (c - b)^1 + (6 : ℝ) * (b - a)^4 * (c - b)^2 + (4 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * a^4 * (c - a)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (5 : ℝ) * a^4 * (b - c)^2 + (12 : ℝ) * a^3 * (c - a)^3 + (14 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^3 * (b - c)^3 + (13 : ℝ) * a^2 * (c - a)^4 + (18 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (10 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (5 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^2 * (b - c)^4 + (6 : ℝ) * a^1 * (c - a)^5 + (10 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1 : ℝ) * (c - a)^6 + (2 : ℝ) * (c - a)^5 * (b - c)^1 + (1 : ℝ) * (c - a)^4 * (b - c)^2 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * c^4 * (a - c)^2 + (6 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (5 : ℝ) * c^4 * (b - a)^2 + (15 : ℝ) * c^3 * (a - c)^3 + (29 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (23 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (5 : ℝ) * c^3 * (b - a)^3 + (16 : ℝ) * c^2 * (a - c)^4 + (42 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (40 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (14 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (1 : ℝ) * c^2 * (b - a)^4 + (7 : ℝ) * c^1 * (a - c)^5 + (23 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (27 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (13 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (2 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (1 : ℝ) * (a - c)^6 + (4 : ℝ) * (a - c)^5 * (b - a)^1 + (6 : ℝ) * (a - c)^4 * (b - a)^2 + (4 : ℝ) * (a - c)^3 * (b - a)^3 + (1 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * b^4 * (a - b)^2 + (6 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (5 : ℝ) * b^4 * (c - a)^2 + (15 : ℝ) * b^3 * (a - b)^3 + (21 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (15 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (5 : ℝ) * b^3 * (c - a)^3 + (16 : ℝ) * b^2 * (a - b)^4 + (26 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (16 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (6 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (1 : ℝ) * b^2 * (c - a)^4 + (7 : ℝ) * b^1 * (a - b)^5 + (13 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (7 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (1 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (1 : ℝ) * (a - b)^6 + (2 : ℝ) * (a - b)^5 * (c - a)^1 + (1 : ℝ) * (a - b)^4 * (c - a)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * b^4 * (c - b)^2 + (4 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^4 * (a - c)^2 + (15 : ℝ) * b^3 * (c - b)^3 + (24 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (18 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (4 : ℝ) * b^3 * (a - c)^3 + (16 : ℝ) * b^2 * (c - b)^4 + (38 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (34 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (12 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (1 : ℝ) * b^2 * (a - c)^4 + (7 : ℝ) * b^1 * (c - b)^5 + (22 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (25 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (12 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (1 : ℝ) * (c - b)^6 + (4 : ℝ) * (c - b)^5 * (a - c)^1 + (6 : ℝ) * (c - b)^4 * (a - c)^2 + (4 : ℝ) * (c - b)^3 * (a - c)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * c^4 * (b - c)^2 + (4 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (4 : ℝ) * c^4 * (a - b)^2 + (15 : ℝ) * c^3 * (b - c)^3 + (16 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (10 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (4 : ℝ) * c^3 * (a - b)^3 + (16 : ℝ) * c^2 * (b - c)^4 + (22 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (10 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (4 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (1 : ℝ) * c^2 * (a - b)^4 + (7 : ℝ) * c^1 * (b - c)^5 + (12 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (5 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (1 : ℝ) * (b - c)^6 + (2 : ℝ) * (b - c)^5 * (a - b)^1 + (1 : ℝ) * (b - c)^4 * (a - b)^2 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (a^4*c^2 + a^2*b^4 + a^2*b^3*c - 5*a^2*b^2*c^2 + a^2*b*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a + 1) ^ 2 ≥ (2 * a + b + c) * (2 / a + 1 / b + 1 / c)) := @solution
#print axioms solution
