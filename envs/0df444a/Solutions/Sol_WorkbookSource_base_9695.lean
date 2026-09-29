-- Prove2me | solution 1 for WorkbookSource.base_9695
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:38.819322+00:00
-- url     : https://prove2.me/submissions/438743f2-26ae-4fd2-b8e8-647b27c6e327

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^3 ≥ (a + b + c) * (a * b + b * c + a * c) * (a^3 + b^3 + c^3)  := by
  have hp : 0 ≤ (a^6 - a^5*b - a^5*c + 2*a^4*b^2 - 3*a^4*b*c + 2*a^4*c^2 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4 - a^2*b^3*c + 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - a*b^5 - 3*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - 3*a*b*c^4 - a*c^5 + b^6 - b^5*c + 2*b^4*c^2 + 2*b^2*c^4 - b*c^5 + c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * a^4 * (b - a)^2 + (3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^4 * (c - b)^2 + (10 : ℝ) * a^3 * (b - a)^3 + (15 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (2 : ℝ) * a^3 * (c - b)^3 + (18 : ℝ) * a^2 * (b - a)^4 + (36 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (33 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^5 + (35 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (44 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (31 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (19 : ℝ) * (b - a)^4 * (c - b)^2 + (18 : ℝ) * (b - a)^3 * (c - b)^3 + (12 : ℝ) * (b - a)^2 * (c - b)^4 + (5 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * a^4 * (c - a)^2 + (3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^4 * (b - c)^2 + (10 : ℝ) * a^3 * (c - a)^3 + (15 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (2 : ℝ) * a^3 * (b - c)^3 + (18 : ℝ) * a^2 * (c - a)^4 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (33 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (15 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^2 * (b - c)^4 + (14 : ℝ) * a^1 * (c - a)^5 + (35 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (44 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (31 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (16 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * a^1 * (b - c)^5 + (4 : ℝ) * (c - a)^6 + (12 : ℝ) * (c - a)^5 * (b - c)^1 + (19 : ℝ) * (c - a)^4 * (b - c)^2 + (18 : ℝ) * (c - a)^3 * (b - c)^3 + (12 : ℝ) * (c - a)^2 * (b - c)^4 + (5 : ℝ) * (c - a)^1 * (b - c)^5 + (1 : ℝ) * (b - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^4 * (a - c)^2 + (3 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (3 : ℝ) * c^4 * (b - a)^2 + (10 : ℝ) * c^3 * (a - c)^3 + (15 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (9 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (2 : ℝ) * c^3 * (b - a)^3 + (18 : ℝ) * c^2 * (a - c)^4 + (36 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (33 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (15 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (6 : ℝ) * c^2 * (b - a)^4 + (14 : ℝ) * c^1 * (a - c)^5 + (35 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (44 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (31 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (16 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (4 : ℝ) * c^1 * (b - a)^5 + (4 : ℝ) * (a - c)^6 + (12 : ℝ) * (a - c)^5 * (b - a)^1 + (19 : ℝ) * (a - c)^4 * (b - a)^2 + (18 : ℝ) * (a - c)^3 * (b - a)^3 + (12 : ℝ) * (a - c)^2 * (b - a)^4 + (5 : ℝ) * (a - c)^1 * (b - a)^5 + (1 : ℝ) * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (3 : ℝ) * b^4 * (a - b)^2 + (3 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (3 : ℝ) * b^4 * (c - a)^2 + (10 : ℝ) * b^3 * (a - b)^3 + (15 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (9 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (2 : ℝ) * b^3 * (c - a)^3 + (18 : ℝ) * b^2 * (a - b)^4 + (36 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (33 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (15 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (6 : ℝ) * b^2 * (c - a)^4 + (14 : ℝ) * b^1 * (a - b)^5 + (35 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (44 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (31 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (16 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (4 : ℝ) * b^1 * (c - a)^5 + (4 : ℝ) * (a - b)^6 + (12 : ℝ) * (a - b)^5 * (c - a)^1 + (19 : ℝ) * (a - b)^4 * (c - a)^2 + (18 : ℝ) * (a - b)^3 * (c - a)^3 + (12 : ℝ) * (a - b)^2 * (c - a)^4 + (5 : ℝ) * (a - b)^1 * (c - a)^5 + (1 : ℝ) * (c - a)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * b^4 * (c - b)^2 + (3 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (3 : ℝ) * b^4 * (a - c)^2 + (10 : ℝ) * b^3 * (c - b)^3 + (15 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (9 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (2 : ℝ) * b^3 * (a - c)^3 + (18 : ℝ) * b^2 * (c - b)^4 + (36 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (33 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (15 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (6 : ℝ) * b^2 * (a - c)^4 + (14 : ℝ) * b^1 * (c - b)^5 + (35 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (44 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (31 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (16 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * b^1 * (a - c)^5 + (4 : ℝ) * (c - b)^6 + (12 : ℝ) * (c - b)^5 * (a - c)^1 + (19 : ℝ) * (c - b)^4 * (a - c)^2 + (18 : ℝ) * (c - b)^3 * (a - c)^3 + (12 : ℝ) * (c - b)^2 * (a - c)^4 + (5 : ℝ) * (c - b)^1 * (a - c)^5 + (1 : ℝ) * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (3 : ℝ) * c^4 * (b - c)^2 + (3 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (3 : ℝ) * c^4 * (a - b)^2 + (10 : ℝ) * c^3 * (b - c)^3 + (15 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (9 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (2 : ℝ) * c^3 * (a - b)^3 + (18 : ℝ) * c^2 * (b - c)^4 + (36 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (33 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (15 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (6 : ℝ) * c^2 * (a - b)^4 + (14 : ℝ) * c^1 * (b - c)^5 + (35 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (44 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (31 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (16 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (4 : ℝ) * c^1 * (a - b)^5 + (4 : ℝ) * (b - c)^6 + (12 : ℝ) * (b - c)^5 * (a - b)^1 + (19 : ℝ) * (b - c)^4 * (a - b)^2 + (18 : ℝ) * (b - c)^3 * (a - b)^3 + (12 : ℝ) * (b - c)^2 * (a - b)^4 + (5 : ℝ) * (b - c)^1 * (a - b)^5 + (1 : ℝ) * (a - b)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2)^3 ≥ (a + b + c) * (a * b + b * c + a * c) * (a^3 + b^3 + c^3)) := @solution
#print axioms solution
