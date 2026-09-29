-- Prove2me | solution 1 for WorkbookSource.base_54671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:51.522424+00:00
-- url     : https://prove2.me/submissions/e67386f2-938e-47d8-979f-69e1a356e1cd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / b + b^3 / c + c^3 / a) ≥ a^2 + b^2 + c^2 + (4 * (a - b)^2 * c^2) / (a^2 + b^2 + c^2)  := by
  have hp : 0 ≤ (a^6*c - a^5*b*c + a^4*b^2*c + a^4*c^3 + a^3*b^4 - 2*a^3*b^3*c - 6*a^3*b*c^3 + 8*a^2*b^2*c^3 + a^2*b*c^4 + a*b^6 - a*b^5*c + a*b^4*c^2 - 6*a*b^3*c^3 - a*b*c^5 + b^3*c^4 + b*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * a^5 * (b - a)^2 + (9 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^5 * (c - b)^2 + (14 : ℝ) * a^4 * (b - a)^3 + (42 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (54 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (15 : ℝ) * a^4 * (c - b)^3 + (18 : ℝ) * a^3 * (b - a)^4 + (72 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (120 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (66 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^3 * (c - b)^4 + (15 : ℝ) * a^2 * (b - a)^5 + (68 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (132 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (108 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (39 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (5 : ℝ) * a^2 * (c - b)^5 + (8 : ℝ) * a^1 * (b - a)^6 + (38 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (78 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (80 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (43 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (11 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^1 * (c - b)^6 + (2 : ℝ) * (b - a)^7 + (10 : ℝ) * (b - a)^6 * (c - b)^1 + (21 : ℝ) * (b - a)^5 * (c - b)^2 + (24 : ℝ) * (b - a)^4 * (c - b)^3 + (16 : ℝ) * (b - a)^3 * (c - b)^4 + (6 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * a^5 * (c - a)^2 + (1 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (5 : ℝ) * a^5 * (b - c)^2 + (14 : ℝ) * a^4 * (c - a)^3 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (11 : ℝ) * a^4 * (b - c)^3 + (18 : ℝ) * a^3 * (c - a)^4 + (12 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (30 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^3 * (b - c)^4 + (15 : ℝ) * a^2 * (c - a)^5 + (7 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (10 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (30 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (22 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (5 : ℝ) * a^2 * (b - c)^5 + (8 : ℝ) * a^1 * (c - a)^6 + (10 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (8 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (12 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (11 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^1 * (b - c)^6 + (2 : ℝ) * (c - a)^7 + (4 : ℝ) * (c - a)^6 * (b - c)^1 + (3 : ℝ) * (c - a)^5 * (b - c)^2 + (1 : ℝ) * (c - a)^4 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^5 * (a - c)^2 + (9 : ℝ) * c^5 * (a - c)^1 * (b - a)^1 + (5 : ℝ) * c^5 * (b - a)^2 + (30 : ℝ) * c^4 * (a - c)^3 + (54 : ℝ) * c^4 * (a - c)^2 * (b - a)^1 + (46 : ℝ) * c^4 * (a - c)^1 * (b - a)^2 + (11 : ℝ) * c^4 * (b - a)^3 + (42 : ℝ) * c^3 * (a - c)^4 + (108 : ℝ) * c^3 * (a - c)^3 * (b - a)^1 + (128 : ℝ) * c^3 * (a - c)^2 * (b - a)^2 + (62 : ℝ) * c^3 * (a - c)^1 * (b - a)^3 + (12 : ℝ) * c^3 * (b - a)^4 + (31 : ℝ) * c^2 * (a - c)^5 + (104 : ℝ) * c^2 * (a - c)^4 * (b - a)^1 + (156 : ℝ) * c^2 * (a - c)^3 * (b - a)^2 + (112 : ℝ) * c^2 * (a - c)^2 * (b - a)^3 + (39 : ℝ) * c^2 * (a - c)^1 * (b - a)^4 + (5 : ℝ) * c^2 * (b - a)^5 + (12 : ℝ) * c^1 * (a - c)^6 + (50 : ℝ) * c^1 * (a - c)^5 * (b - a)^1 + (90 : ℝ) * c^1 * (a - c)^4 * (b - a)^2 + (84 : ℝ) * c^1 * (a - c)^3 * (b - a)^3 + (43 : ℝ) * c^1 * (a - c)^2 * (b - a)^4 + (11 : ℝ) * c^1 * (a - c)^1 * (b - a)^5 + (1 : ℝ) * c^1 * (b - a)^6 + (2 : ℝ) * (a - c)^7 + (10 : ℝ) * (a - c)^6 * (b - a)^1 + (21 : ℝ) * (a - c)^5 * (b - a)^2 + (24 : ℝ) * (a - c)^4 * (b - a)^3 + (16 : ℝ) * (a - c)^3 * (b - a)^4 + (6 : ℝ) * (a - c)^2 * (b - a)^5 + (1 : ℝ) * (a - c)^1 * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * b^5 * (a - b)^2 + (9 : ℝ) * b^5 * (a - b)^1 * (c - a)^1 + (9 : ℝ) * b^5 * (c - a)^2 + (14 : ℝ) * b^4 * (a - b)^3 + (24 : ℝ) * b^4 * (a - b)^2 * (c - a)^1 + (36 : ℝ) * b^4 * (a - b)^1 * (c - a)^2 + (15 : ℝ) * b^4 * (c - a)^3 + (18 : ℝ) * b^3 * (a - b)^4 + (24 : ℝ) * b^3 * (a - b)^3 * (c - a)^1 + (48 : ℝ) * b^3 * (a - b)^2 * (c - a)^2 + (42 : ℝ) * b^3 * (a - b)^1 * (c - a)^3 + (12 : ℝ) * b^3 * (c - a)^4 + (15 : ℝ) * b^2 * (a - b)^5 + (15 : ℝ) * b^2 * (a - b)^4 * (c - a)^1 + (26 : ℝ) * b^2 * (a - b)^3 * (c - a)^2 + (38 : ℝ) * b^2 * (a - b)^2 * (c - a)^3 + (22 : ℝ) * b^2 * (a - b)^1 * (c - a)^4 + (5 : ℝ) * b^2 * (c - a)^5 + (8 : ℝ) * b^1 * (a - b)^6 + (10 : ℝ) * b^1 * (a - b)^5 * (c - a)^1 + (8 : ℝ) * b^1 * (a - b)^4 * (c - a)^2 + (12 : ℝ) * b^1 * (a - b)^3 * (c - a)^3 + (11 : ℝ) * b^1 * (a - b)^2 * (c - a)^4 + (5 : ℝ) * b^1 * (a - b)^1 * (c - a)^5 + (1 : ℝ) * b^1 * (c - a)^6 + (2 : ℝ) * (a - b)^7 + (4 : ℝ) * (a - b)^6 * (c - a)^1 + (3 : ℝ) * (a - b)^5 * (c - a)^2 + (1 : ℝ) * (a - b)^4 * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * b^5 * (c - b)^2 + (1 : ℝ) * b^5 * (c - b)^1 * (a - c)^1 + (5 : ℝ) * b^5 * (a - c)^2 + (14 : ℝ) * b^4 * (c - b)^3 + (18 : ℝ) * b^4 * (c - b)^2 * (a - c)^1 + (30 : ℝ) * b^4 * (c - b)^1 * (a - c)^2 + (11 : ℝ) * b^4 * (a - c)^3 + (18 : ℝ) * b^3 * (c - b)^4 + (48 : ℝ) * b^3 * (c - b)^3 * (a - c)^1 + (84 : ℝ) * b^3 * (c - b)^2 * (a - c)^2 + (54 : ℝ) * b^3 * (c - b)^1 * (a - c)^3 + (12 : ℝ) * b^3 * (a - c)^4 + (15 : ℝ) * b^2 * (c - b)^5 + (60 : ℝ) * b^2 * (c - b)^4 * (a - c)^1 + (116 : ℝ) * b^2 * (c - b)^3 * (a - c)^2 + (100 : ℝ) * b^2 * (c - b)^2 * (a - c)^3 + (39 : ℝ) * b^2 * (c - b)^1 * (a - c)^4 + (5 : ℝ) * b^2 * (a - c)^5 + (8 : ℝ) * b^1 * (c - b)^6 + (38 : ℝ) * b^1 * (c - b)^5 * (a - c)^1 + (78 : ℝ) * b^1 * (c - b)^4 * (a - c)^2 + (80 : ℝ) * b^1 * (c - b)^3 * (a - c)^3 + (43 : ℝ) * b^1 * (c - b)^2 * (a - c)^4 + (11 : ℝ) * b^1 * (c - b)^1 * (a - c)^5 + (1 : ℝ) * b^1 * (a - c)^6 + (2 : ℝ) * (c - b)^7 + (10 : ℝ) * (c - b)^6 * (a - c)^1 + (21 : ℝ) * (c - b)^5 * (a - c)^2 + (24 : ℝ) * (c - b)^4 * (a - c)^3 + (16 : ℝ) * (c - b)^3 * (a - c)^4 + (6 : ℝ) * (c - b)^2 * (a - c)^5 + (1 : ℝ) * (c - b)^1 * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^5 * (b - c)^2 + (9 : ℝ) * c^5 * (b - c)^1 * (a - b)^1 + (5 : ℝ) * c^5 * (a - b)^2 + (30 : ℝ) * c^4 * (b - c)^3 + (36 : ℝ) * c^4 * (b - c)^2 * (a - b)^1 + (28 : ℝ) * c^4 * (b - c)^1 * (a - b)^2 + (11 : ℝ) * c^4 * (a - b)^3 + (42 : ℝ) * c^3 * (b - c)^4 + (60 : ℝ) * c^3 * (b - c)^3 * (a - b)^1 + (56 : ℝ) * c^3 * (b - c)^2 * (a - b)^2 + (38 : ℝ) * c^3 * (b - c)^1 * (a - b)^3 + (12 : ℝ) * c^3 * (a - b)^4 + (31 : ℝ) * c^2 * (b - c)^5 + (51 : ℝ) * c^2 * (b - c)^4 * (a - b)^1 + (50 : ℝ) * c^2 * (b - c)^3 * (a - b)^2 + (42 : ℝ) * c^2 * (b - c)^2 * (a - b)^3 + (22 : ℝ) * c^2 * (b - c)^1 * (a - b)^4 + (5 : ℝ) * c^2 * (a - b)^5 + (12 : ℝ) * c^1 * (b - c)^6 + (22 : ℝ) * c^1 * (b - c)^5 * (a - b)^1 + (20 : ℝ) * c^1 * (b - c)^4 * (a - b)^2 + (16 : ℝ) * c^1 * (b - c)^3 * (a - b)^3 + (11 : ℝ) * c^1 * (b - c)^2 * (a - b)^4 + (5 : ℝ) * c^1 * (b - c)^1 * (a - b)^5 + (1 : ℝ) * c^1 * (a - b)^6 + (2 : ℝ) * (b - c)^7 + (4 : ℝ) * (b - c)^6 * (a - b)^1 + (3 : ℝ) * (b - c)^5 * (a - b)^2 + (1 : ℝ) * (b - c)^4 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (a^6*c - a^5*b*c + a^4*b^2*c + a^4*c^3 + a^3*b^4 - 2*a^3*b^3*c - 6*a^3*b*c^3 + 8*a^2*b^2*c^3 + a^2*b*c^4 + a*b^6 - a*b^5*c + a*b^4*c^2 - 6*a*b^3*c^3 - a*b*c^5 + b^3*c^4 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / b + b^3 / c + c^3 / a) ≥ a^2 + b^2 + c^2 + (4 * (a - b)^2 * c^2) / (a^2 + b^2 + c^2)) := @solution
#print axioms solution
