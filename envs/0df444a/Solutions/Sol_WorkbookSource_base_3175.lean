-- Prove2me | solution 1 for WorkbookSource.base_3175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:15.84788+00:00
-- url     : https://prove2.me/submissions/87e68193-f2ec-4aeb-9793-450ae730dc5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 1 / 2 * (b / (a + c) + (b + 2 * a) / (b + c) + (b + 2 * c) / (a + b) + 5 / 2)  := by
  have hp : 0 ≤ (4*a^4*c^2 + 4*a^3*b^3 - 3*a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 3*a^2*b^3*c - 12*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 4*b^3*c^3 + 4*b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (20 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (76 : ℝ) * a^3 * (b - a)^3 + (119 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (89 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (20 : ℝ) * a^3 * (c - b)^3 + (88 : ℝ) * a^2 * (b - a)^4 + (198 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (165 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (53 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (44 : ℝ) * a^1 * (b - a)^5 + (127 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (132 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (57 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * (b - a)^6 + (28 : ℝ) * (b - a)^5 * (c - b)^1 + (36 : ℝ) * (b - a)^4 * (c - b)^2 + (20 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (24 : ℝ) * a^4 * (c - a)^2 + (28 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (28 : ℝ) * a^4 * (b - c)^2 + (76 : ℝ) * a^3 * (c - a)^3 + (109 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (79 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (26 : ℝ) * a^3 * (b - c)^3 + (88 : ℝ) * a^2 * (c - a)^4 + (154 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (99 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (35 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^2 * (b - c)^4 + (44 : ℝ) * a^1 * (c - a)^5 + (93 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (64 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (17 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (8 : ℝ) * (c - a)^6 + (20 : ℝ) * (c - a)^5 * (b - c)^1 + (16 : ℝ) * (c - a)^4 * (b - c)^2 + (4 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (24 : ℝ) * c^4 * (a - c)^2 + (28 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (28 : ℝ) * c^4 * (b - a)^2 + (76 : ℝ) * c^3 * (a - c)^3 + (141 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (111 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (26 : ℝ) * c^3 * (b - a)^3 + (88 : ℝ) * c^2 * (a - c)^4 + (218 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (195 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (67 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (6 : ℝ) * c^2 * (b - a)^4 + (44 : ℝ) * c^1 * (a - c)^5 + (133 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (144 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (65 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (10 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (8 : ℝ) * (a - c)^6 + (28 : ℝ) * (a - c)^5 * (b - a)^1 + (36 : ℝ) * (a - c)^4 * (b - a)^2 + (20 : ℝ) * (a - c)^3 * (b - a)^3 + (4 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (28 : ℝ) * b^4 * (a - b)^2 + (28 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (24 : ℝ) * b^4 * (c - a)^2 + (86 : ℝ) * b^3 * (a - b)^3 + (113 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (67 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (20 : ℝ) * b^3 * (c - a)^3 + (96 : ℝ) * b^2 * (a - b)^4 + (160 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (87 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (23 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (4 : ℝ) * b^2 * (c - a)^4 + (46 : ℝ) * b^1 * (a - b)^5 + (95 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (60 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (11 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (8 : ℝ) * (a - b)^6 + (20 : ℝ) * (a - b)^5 * (c - a)^1 + (16 : ℝ) * (a - b)^4 * (c - a)^2 + (4 : ℝ) * (a - b)^3 * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (28 : ℝ) * b^4 * (c - b)^2 + (28 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (24 : ℝ) * b^4 * (a - c)^2 + (86 : ℝ) * b^3 * (c - b)^3 + (145 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (99 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (20 : ℝ) * b^3 * (a - c)^3 + (96 : ℝ) * b^2 * (c - b)^4 + (224 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (183 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (55 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (4 : ℝ) * b^2 * (a - c)^4 + (46 : ℝ) * b^1 * (c - b)^5 + (135 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (140 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (59 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (8 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (8 : ℝ) * (c - b)^6 + (28 : ℝ) * (c - b)^5 * (a - c)^1 + (36 : ℝ) * (c - b)^4 * (a - c)^2 + (20 : ℝ) * (c - b)^3 * (a - c)^3 + (4 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (24 : ℝ) * c^4 * (b - c)^2 + (20 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (24 : ℝ) * c^4 * (a - b)^2 + (76 : ℝ) * c^3 * (b - c)^3 + (87 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (57 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (20 : ℝ) * c^3 * (a - b)^3 + (88 : ℝ) * c^2 * (b - c)^4 + (134 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (69 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (21 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (4 : ℝ) * c^2 * (a - b)^4 + (44 : ℝ) * c^1 * (b - c)^5 + (87 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (52 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (9 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (8 : ℝ) * (b - c)^6 + (20 : ℝ) * (b - c)^5 * (a - b)^1 + (16 : ℝ) * (b - c)^4 * (a - b)^2 + (4 : ℝ) * (b - c)^3 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (4*a^4*c^2 + 4*a^3*b^3 - 3*a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 3*a^2*b^3*c - 12*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 4*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ≥ 1 / 2 * (b / (a + c) + (b + 2 * a) / (b + c) + (b + 2 * c) / (a + b) + 5 / 2)) := @solution
#print axioms solution
