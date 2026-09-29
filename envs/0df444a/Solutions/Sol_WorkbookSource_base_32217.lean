-- Prove2me | solution 1 for WorkbookSource.base_32217
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:03.533252+00:00
-- url     : https://prove2.me/submissions/b3118ff6-3165-4dd0-846d-9e2f22c6d4e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 2 / (a + b) + 3 / (a + b + c)) ≤ (4 / 3) * (1 / a + 1 / b + 1 / c)  := by
  have hp : 0 ≤ (4*a^3*b + 4*a^3*c + 8*a^2*b^2 - 2*a^2*b*c + 4*a^2*c^2 + 4*a*b^3 - 5*a*b^2*c - a*b*c^2 + b^3*c + b^2*c^2) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (18 : ℝ) * a^4 + (30 : ℝ) * a^3 * (b - a)^1 + (6 : ℝ) * a^3 * (c - b)^1 + (16 : ℝ) * a^2 * (b - a)^2 + (1 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^2 * (c - b)^2 + (6 : ℝ) * a^1 * (b - a)^3 + (2 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (2 : ℝ) * (b - a)^4 + (3 : ℝ) * (b - a)^3 * (c - b)^1 + (1 : ℝ) * (b - a)^2 * (c - b)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (18 : ℝ) * a^4 + (30 : ℝ) * a^3 * (c - a)^1 + (24 : ℝ) * a^3 * (b - c)^1 + (16 : ℝ) * a^2 * (c - a)^2 + (31 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (19 : ℝ) * a^2 * (b - c)^2 + (6 : ℝ) * a^1 * (c - a)^3 + (16 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^1 * (b - c)^3 + (2 : ℝ) * (c - a)^4 + (5 : ℝ) * (c - a)^3 * (b - c)^1 + (4 : ℝ) * (c - a)^2 * (b - c)^2 + (1 : ℝ) * (c - a)^1 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (18 : ℝ) * c^4 + (66 : ℝ) * c^3 * (a - c)^1 + (24 : ℝ) * c^3 * (b - a)^1 + (94 : ℝ) * c^2 * (a - c)^2 + (79 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (19 : ℝ) * c^2 * (b - a)^2 + (62 : ℝ) * c^1 * (a - c)^3 + (87 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (38 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (5 : ℝ) * c^1 * (b - a)^3 + (16 : ℝ) * (a - c)^4 + (32 : ℝ) * (a - c)^3 * (b - a)^1 + (20 : ℝ) * (a - c)^2 * (b - a)^2 + (4 : ℝ) * (a - c)^1 * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (18 : ℝ) * b^4 + (48 : ℝ) * b^3 * (a - b)^1 + (6 : ℝ) * b^3 * (c - a)^1 + (55 : ℝ) * b^2 * (a - b)^2 + (25 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (4 : ℝ) * b^2 * (c - a)^2 + (33 : ℝ) * b^1 * (a - b)^3 + (32 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (7 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (8 : ℝ) * (a - b)^4 + (12 : ℝ) * (a - b)^3 * (c - a)^1 + (4 : ℝ) * (a - b)^2 * (c - a)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (18 : ℝ) * b^4 + (48 : ℝ) * b^3 * (c - b)^1 + (42 : ℝ) * b^3 * (a - c)^1 + (55 : ℝ) * b^2 * (c - b)^2 + (85 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (34 : ℝ) * b^2 * (a - c)^2 + (33 : ℝ) * b^1 * (c - b)^3 + (67 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (42 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (8 : ℝ) * b^1 * (a - c)^3 + (8 : ℝ) * (c - b)^4 + (20 : ℝ) * (c - b)^3 * (a - c)^1 + (16 : ℝ) * (c - b)^2 * (a - c)^2 + (4 : ℝ) * (c - b)^1 * (a - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (18 : ℝ) * c^4 + (66 : ℝ) * c^3 * (b - c)^1 + (42 : ℝ) * c^3 * (a - b)^1 + (94 : ℝ) * c^2 * (b - c)^2 + (109 : ℝ) * c^2 * (b - c)^1 * (a - b)^1 + (34 : ℝ) * c^2 * (a - b)^2 + (62 : ℝ) * c^1 * (b - c)^3 + (99 : ℝ) * c^1 * (b - c)^2 * (a - b)^1 + (50 : ℝ) * c^1 * (b - c)^1 * (a - b)^2 + (8 : ℝ) * c^1 * (a - b)^3 + (16 : ℝ) * (b - c)^4 + (32 : ℝ) * (b - c)^3 * (a - b)^1 + (20 : ℝ) * (b - c)^2 * (a - b)^2 + (4 : ℝ) * (b - c)^1 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (4*a^3*b + 4*a^3*c + 8*a^2*b^2 - 2*a^2*b*c + 4*a^2*c^2 + 4*a*b^3 - 5*a*b^2*c - a*b*c^2 + b^3*c + b^2*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / a + 2 / (a + b) + 3 / (a + b + c)) ≤ (4 / 3) * (1 / a + 1 / b + 1 / c)) := @solution
#print axioms solution
