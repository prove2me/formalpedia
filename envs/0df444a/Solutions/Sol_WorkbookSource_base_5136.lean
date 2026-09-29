-- Prove2me | solution 1 for WorkbookSource.base_5136
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:28.248703+00:00
-- url     : https://prove2.me/submissions/38250bc2-7798-4647-aee9-2026df722e0f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b^3 + b^3 * c^3 + c^3 * a^3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a^3 + b^3 + c^3)  := by
  have hp : 0 ≤ (a^6 - a^5*b - a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 + 3*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 3*a^3*c^3 - a^2*b^4 - a^2*b^3*c - a^2*b*c^3 - a^2*c^4 - a*b^5 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 - a*c^5 + b^6 - b^5*c - b^4*c^2 + 3*b^3*c^3 - b^2*c^4 - b*c^5 + c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^4 * (b - a)^2 + (3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^4 * (c - b)^2 + (8 : ℝ) * a^3 * (b - a)^3 + (12 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (12 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (11 : ℝ) * a^2 * (b - a)^4 + (22 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (16 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (5 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (26 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (24 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (1 : ℝ) * (b - a)^6 + (3 : ℝ) * (b - a)^5 * (c - b)^1 + (7 : ℝ) * (b - a)^4 * (c - b)^2 + (9 : ℝ) * (b - a)^3 * (c - b)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^4 + (5 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^4 * (c - a)^2 + (3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^4 * (b - c)^2 + (8 : ℝ) * a^3 * (c - a)^3 + (12 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^3 * (b - c)^3 + (11 : ℝ) * a^2 * (c - a)^4 + (22 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (27 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (16 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (5 : ℝ) * a^2 * (b - c)^4 + (6 : ℝ) * a^1 * (c - a)^5 + (15 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (26 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (24 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (15 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * a^1 * (b - c)^5 + (1 : ℝ) * (c - a)^6 + (3 : ℝ) * (c - a)^5 * (b - c)^1 + (7 : ℝ) * (c - a)^4 * (b - c)^2 + (9 : ℝ) * (c - a)^3 * (b - c)^3 + (9 : ℝ) * (c - a)^2 * (b - c)^4 + (5 : ℝ) * (c - a)^1 * (b - c)^5 + (1 : ℝ) * (b - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^4 * (a - c)^2 + (3 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (3 : ℝ) * c^4 * (b - a)^2 + (8 : ℝ) * c^3 * (a - c)^3 + (12 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (12 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (4 : ℝ) * c^3 * (b - a)^3 + (11 : ℝ) * c^2 * (a - c)^4 + (22 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (27 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (16 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (5 : ℝ) * c^2 * (b - a)^4 + (6 : ℝ) * c^1 * (a - c)^5 + (15 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (26 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (24 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (15 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (4 : ℝ) * c^1 * (b - a)^5 + (1 : ℝ) * (a - c)^6 + (3 : ℝ) * (a - c)^5 * (b - a)^1 + (7 : ℝ) * (a - c)^4 * (b - a)^2 + (9 : ℝ) * (a - c)^3 * (b - a)^3 + (9 : ℝ) * (a - c)^2 * (b - a)^4 + (5 : ℝ) * (a - c)^1 * (b - a)^5 + (1 : ℝ) * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * b^4 * (a - b)^2 + (3 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (3 : ℝ) * b^4 * (c - a)^2 + (8 : ℝ) * b^3 * (a - b)^3 + (12 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (12 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (4 : ℝ) * b^3 * (c - a)^3 + (11 : ℝ) * b^2 * (a - b)^4 + (22 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (27 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (16 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (5 : ℝ) * b^2 * (c - a)^4 + (6 : ℝ) * b^1 * (a - b)^5 + (15 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (26 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (24 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (15 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (4 : ℝ) * b^1 * (c - a)^5 + (1 : ℝ) * (a - b)^6 + (3 : ℝ) * (a - b)^5 * (c - a)^1 + (7 : ℝ) * (a - b)^4 * (c - a)^2 + (9 : ℝ) * (a - b)^3 * (c - a)^3 + (9 : ℝ) * (a - b)^2 * (c - a)^4 + (5 : ℝ) * (a - b)^1 * (c - a)^5 + (1 : ℝ) * (c - a)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * b^4 * (c - b)^2 + (3 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (3 : ℝ) * b^4 * (a - c)^2 + (8 : ℝ) * b^3 * (c - b)^3 + (12 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (12 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (4 : ℝ) * b^3 * (a - c)^3 + (11 : ℝ) * b^2 * (c - b)^4 + (22 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (27 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (16 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (5 : ℝ) * b^2 * (a - c)^4 + (6 : ℝ) * b^1 * (c - b)^5 + (15 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (26 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (24 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (15 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * b^1 * (a - c)^5 + (1 : ℝ) * (c - b)^6 + (3 : ℝ) * (c - b)^5 * (a - c)^1 + (7 : ℝ) * (c - b)^4 * (a - c)^2 + (9 : ℝ) * (c - b)^3 * (a - c)^3 + (9 : ℝ) * (c - b)^2 * (a - c)^4 + (5 : ℝ) * (c - b)^1 * (a - c)^5 + (1 : ℝ) * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^4 * (b - c)^2 + (3 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (3 : ℝ) * c^4 * (a - b)^2 + (8 : ℝ) * c^3 * (b - c)^3 + (12 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (12 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (4 : ℝ) * c^3 * (a - b)^3 + (11 : ℝ) * c^2 * (b - c)^4 + (22 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (27 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (16 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (5 : ℝ) * c^2 * (a - b)^4 + (6 : ℝ) * c^1 * (b - c)^5 + (15 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (26 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (24 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (15 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (4 : ℝ) * c^1 * (a - b)^5 + (1 : ℝ) * (b - c)^6 + (3 : ℝ) * (b - c)^5 * (a - b)^1 + (7 : ℝ) * (b - c)^4 * (a - b)^2 + (9 : ℝ) * (b - c)^3 * (a - b)^3 + (9 : ℝ) * (b - c)^2 * (a - b)^4 + (5 : ℝ) * (b - c)^1 * (a - b)^5 + (1 : ℝ) * (a - b)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^3 * b^3 + b^3 * c^3 + c^3 * a^3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a^3 + b^3 + c^3)) := @solution
#print axioms solution
