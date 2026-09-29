-- Prove2me | solution 1 for WorkbookSource.base_18130
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:39.926218+00:00
-- url     : https://prove2.me/submissions/9550f3b8-dd87-49dd-9c36-71f94fa54391

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / b + b^3 / c^2 + c^4 / a^3 ≥ -a + 2 * b + 2 * c  := by
  have hp : 0 ≤ (a^5*c^2 + a^4*b*c^2 + a^3*b^4 - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 + b*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (7 : ℝ) * a^5 * (b - a)^2 + (12 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^5 * (c - b)^2 + (24 : ℝ) * a^4 * (b - a)^3 + (62 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (60 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^4 * (c - b)^3 + (32 : ℝ) * a^3 * (b - a)^4 + (110 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (142 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (78 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (15 : ℝ) * a^3 * (c - b)^4 + (21 : ℝ) * a^2 * (b - a)^5 + (90 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (150 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (120 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^2 * (c - b)^5 + (7 : ℝ) * a^1 * (b - a)^6 + (36 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (75 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (80 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (45 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^1 * (c - b)^6 + (1 : ℝ) * (b - a)^7 + (6 : ℝ) * (b - a)^6 * (c - b)^1 + (15 : ℝ) * (b - a)^5 * (c - b)^2 + (20 : ℝ) * (b - a)^4 * (c - b)^3 + (15 : ℝ) * (b - a)^3 * (c - b)^4 + (6 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (7 : ℝ) * a^5 * (c - a)^2 + (2 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^5 * (b - c)^2 + (24 : ℝ) * a^4 * (c - a)^3 + (10 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^4 * (b - c)^3 + (32 : ℝ) * a^3 * (c - a)^4 + (18 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (4 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^3 * (b - c)^4 + (21 : ℝ) * a^2 * (c - a)^5 + (15 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (7 : ℝ) * a^1 * (c - a)^6 + (6 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (1 : ℝ) * (c - a)^7 + (1 : ℝ) * (c - a)^6 * (b - c)^1 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^5 * (a - c)^2 + (6 : ℝ) * c^5 * (a - c)^1 * (b - a)^1 + (4 : ℝ) * c^5 * (b - a)^2 + (27 : ℝ) * c^4 * (a - c)^3 + (36 : ℝ) * c^4 * (a - c)^2 * (b - a)^1 + (24 : ℝ) * c^4 * (a - c)^1 * (b - a)^2 + (4 : ℝ) * c^4 * (b - a)^3 + (33 : ℝ) * c^3 * (a - c)^4 + (66 : ℝ) * c^3 * (a - c)^3 * (b - a)^1 + (54 : ℝ) * c^3 * (a - c)^2 * (b - a)^2 + (16 : ℝ) * c^3 * (a - c)^1 * (b - a)^3 + (1 : ℝ) * c^3 * (b - a)^4 + (21 : ℝ) * c^2 * (a - c)^5 + (57 : ℝ) * c^2 * (a - c)^4 * (b - a)^1 + (58 : ℝ) * c^2 * (a - c)^3 * (b - a)^2 + (24 : ℝ) * c^2 * (a - c)^2 * (b - a)^3 + (3 : ℝ) * c^2 * (a - c)^1 * (b - a)^4 + (7 : ℝ) * c^1 * (a - c)^6 + (24 : ℝ) * c^1 * (a - c)^5 * (b - a)^1 + (30 : ℝ) * c^1 * (a - c)^4 * (b - a)^2 + (16 : ℝ) * c^1 * (a - c)^3 * (b - a)^3 + (3 : ℝ) * c^1 * (a - c)^2 * (b - a)^4 + (1 : ℝ) * (a - c)^7 + (4 : ℝ) * (a - c)^6 * (b - a)^1 + (6 : ℝ) * (a - c)^5 * (b - a)^2 + (4 : ℝ) * (a - c)^4 * (b - a)^3 + (1 : ℝ) * (a - c)^3 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * b^5 * (a - b)^2 + (6 : ℝ) * b^5 * (a - b)^1 * (c - a)^1 + (9 : ℝ) * b^5 * (c - a)^2 + (16 : ℝ) * b^4 * (a - b)^3 + (26 : ℝ) * b^4 * (a - b)^2 * (c - a)^1 + (39 : ℝ) * b^4 * (a - b)^1 * (c - a)^2 + (18 : ℝ) * b^4 * (c - a)^3 + (25 : ℝ) * b^3 * (a - b)^4 + (44 : ℝ) * b^3 * (a - b)^3 * (c - a)^1 + (64 : ℝ) * b^3 * (a - b)^2 * (c - a)^2 + (54 : ℝ) * b^3 * (a - b)^1 * (c - a)^3 + (15 : ℝ) * b^3 * (c - a)^4 + (19 : ℝ) * b^2 * (a - b)^5 + (36 : ℝ) * b^2 * (a - b)^4 * (c - a)^1 + (48 : ℝ) * b^2 * (a - b)^3 * (c - a)^2 + (54 : ℝ) * b^2 * (a - b)^2 * (c - a)^3 + (30 : ℝ) * b^2 * (a - b)^1 * (c - a)^4 + (6 : ℝ) * b^2 * (c - a)^5 + (7 : ℝ) * b^1 * (a - b)^6 + (14 : ℝ) * b^1 * (a - b)^5 * (c - a)^1 + (15 : ℝ) * b^1 * (a - b)^4 * (c - a)^2 + (18 : ℝ) * b^1 * (a - b)^3 * (c - a)^3 + (15 : ℝ) * b^1 * (a - b)^2 * (c - a)^4 + (6 : ℝ) * b^1 * (a - b)^1 * (c - a)^5 + (1 : ℝ) * b^1 * (c - a)^6 + (1 : ℝ) * (a - b)^7 + (2 : ℝ) * (a - b)^6 * (c - a)^1 + (1 : ℝ) * (a - b)^5 * (c - a)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * b^5 * (c - b)^2 + (2 : ℝ) * b^5 * (c - b)^1 * (a - c)^1 + (7 : ℝ) * b^5 * (a - c)^2 + (16 : ℝ) * b^4 * (c - b)^3 + (22 : ℝ) * b^4 * (c - b)^2 * (a - c)^1 + (35 : ℝ) * b^4 * (c - b)^1 * (a - c)^2 + (11 : ℝ) * b^4 * (a - c)^3 + (25 : ℝ) * b^3 * (c - b)^4 + (56 : ℝ) * b^3 * (c - b)^3 * (a - c)^1 + (82 : ℝ) * b^3 * (c - b)^2 * (a - c)^2 + (42 : ℝ) * b^3 * (c - b)^1 * (a - c)^3 + (6 : ℝ) * b^3 * (a - c)^4 + (19 : ℝ) * b^2 * (c - b)^5 + (59 : ℝ) * b^2 * (c - b)^4 * (a - c)^1 + (94 : ℝ) * b^2 * (c - b)^3 * (a - c)^2 + (64 : ℝ) * b^2 * (c - b)^2 * (a - c)^3 + (17 : ℝ) * b^2 * (c - b)^1 * (a - c)^4 + (1 : ℝ) * b^2 * (a - c)^5 + (7 : ℝ) * b^1 * (c - b)^6 + (28 : ℝ) * b^1 * (c - b)^5 * (a - c)^1 + (50 : ℝ) * b^1 * (c - b)^4 * (a - c)^2 + (42 : ℝ) * b^1 * (c - b)^3 * (a - c)^3 + (16 : ℝ) * b^1 * (c - b)^2 * (a - c)^4 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^5 + (1 : ℝ) * (c - b)^7 + (5 : ℝ) * (c - b)^6 * (a - c)^1 + (10 : ℝ) * (c - b)^5 * (a - c)^2 + (10 : ℝ) * (c - b)^4 * (a - c)^3 + (5 : ℝ) * (c - b)^3 * (a - c)^4 + (1 : ℝ) * (c - b)^2 * (a - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^5 * (b - c)^2 + (12 : ℝ) * c^5 * (b - c)^1 * (a - b)^1 + (7 : ℝ) * c^5 * (a - b)^2 + (27 : ℝ) * c^4 * (b - c)^3 + (45 : ℝ) * c^4 * (b - c)^2 * (a - b)^1 + (33 : ℝ) * c^4 * (b - c)^1 * (a - b)^2 + (11 : ℝ) * c^4 * (a - b)^3 + (33 : ℝ) * c^3 * (b - c)^4 + (66 : ℝ) * c^3 * (b - c)^3 * (a - b)^1 + (54 : ℝ) * c^3 * (b - c)^2 * (a - b)^2 + (26 : ℝ) * c^3 * (b - c)^1 * (a - b)^3 + (6 : ℝ) * c^3 * (a - b)^4 + (21 : ℝ) * c^2 * (b - c)^5 + (48 : ℝ) * c^2 * (b - c)^4 * (a - b)^1 + (40 : ℝ) * c^2 * (b - c)^3 * (a - b)^2 + (18 : ℝ) * c^2 * (b - c)^2 * (a - b)^3 + (6 : ℝ) * c^2 * (b - c)^1 * (a - b)^4 + (1 : ℝ) * c^2 * (a - b)^5 + (7 : ℝ) * c^1 * (b - c)^6 + (18 : ℝ) * c^1 * (b - c)^5 * (a - b)^1 + (15 : ℝ) * c^1 * (b - c)^4 * (a - b)^2 + (4 : ℝ) * c^1 * (b - c)^3 * (a - b)^3 + (1 : ℝ) * (b - c)^7 + (3 : ℝ) * (b - c)^6 * (a - b)^1 + (3 : ℝ) * (b - c)^5 * (a - b)^2 + (1 : ℝ) * (b - c)^4 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (a^5*c^2 + a^4*b*c^2 + a^3*b^4 - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 / b + b^3 / c^2 + c^4 / a^3 ≥ -a + 2 * b + 2 * c) := @solution
#print axioms solution
