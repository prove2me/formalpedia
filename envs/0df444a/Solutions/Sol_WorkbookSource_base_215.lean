-- Prove2me | solution 1 for WorkbookSource.base_215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:28.228221+00:00
-- url     : https://prove2.me/submissions/b505009a-009f-40b1-8a9f-c56f14b4dbbf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 / 2 + a / (b + c) + b / (a + c) + c / (a + b)  := by
  have hp : 0 ≤ (2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 - a*b^3*c^2 - a*b^2*c^3 + 2*b^3*c^3 + 2*b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (38 : ℝ) * a^3 * (b - a)^3 + (65 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (47 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^3 * (c - b)^3 + (44 : ℝ) * a^2 * (b - a)^4 + (104 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (87 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (22 : ℝ) * a^1 * (b - a)^5 + (65 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (68 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (29 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (14 : ℝ) * (b - a)^5 * (c - b)^1 + (18 : ℝ) * (b - a)^4 * (c - b)^2 + (10 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * a^4 * (c - a)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^4 * (b - c)^2 + (38 : ℝ) * a^3 * (c - a)^3 + (49 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (31 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (10 : ℝ) * a^3 * (b - c)^3 + (44 : ℝ) * a^2 * (c - a)^4 + (72 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (39 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (11 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (22 : ℝ) * a^1 * (c - a)^5 + (45 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (28 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (5 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (4 : ℝ) * (c - a)^6 + (10 : ℝ) * (c - a)^5 * (b - c)^1 + (8 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^4 * (a - c)^2 + (12 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (12 : ℝ) * c^4 * (b - a)^2 + (38 : ℝ) * c^3 * (a - c)^3 + (65 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (47 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (10 : ℝ) * c^3 * (b - a)^3 + (44 : ℝ) * c^2 * (a - c)^4 + (104 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (87 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (27 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (2 : ℝ) * c^2 * (b - a)^4 + (22 : ℝ) * c^1 * (a - c)^5 + (65 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (68 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (29 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (4 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (4 : ℝ) * (a - c)^6 + (14 : ℝ) * (a - c)^5 * (b - a)^1 + (18 : ℝ) * (a - c)^4 * (b - a)^2 + (10 : ℝ) * (a - c)^3 * (b - a)^3 + (2 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * b^4 * (a - b)^2 + (12 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (12 : ℝ) * b^4 * (c - a)^2 + (38 : ℝ) * b^3 * (a - b)^3 + (49 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (31 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (10 : ℝ) * b^3 * (c - a)^3 + (44 : ℝ) * b^2 * (a - b)^4 + (72 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (39 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (11 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (2 : ℝ) * b^2 * (c - a)^4 + (22 : ℝ) * b^1 * (a - b)^5 + (45 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (28 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (5 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (4 : ℝ) * (a - b)^6 + (10 : ℝ) * (a - b)^5 * (c - a)^1 + (8 : ℝ) * (a - b)^4 * (c - a)^2 + (2 : ℝ) * (a - b)^3 * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * b^4 * (c - b)^2 + (12 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (12 : ℝ) * b^4 * (a - c)^2 + (38 : ℝ) * b^3 * (c - b)^3 + (65 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (47 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (10 : ℝ) * b^3 * (a - c)^3 + (44 : ℝ) * b^2 * (c - b)^4 + (104 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (87 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (27 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (2 : ℝ) * b^2 * (a - c)^4 + (22 : ℝ) * b^1 * (c - b)^5 + (65 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (68 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (29 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (4 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * (c - b)^6 + (14 : ℝ) * (c - b)^5 * (a - c)^1 + (18 : ℝ) * (c - b)^4 * (a - c)^2 + (10 : ℝ) * (c - b)^3 * (a - c)^3 + (2 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^4 * (b - c)^2 + (12 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (12 : ℝ) * c^4 * (a - b)^2 + (38 : ℝ) * c^3 * (b - c)^3 + (49 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (31 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (10 : ℝ) * c^3 * (a - b)^3 + (44 : ℝ) * c^2 * (b - c)^4 + (72 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (39 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (11 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (2 : ℝ) * c^2 * (a - b)^4 + (22 : ℝ) * c^1 * (b - c)^5 + (45 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (28 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (5 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (4 : ℝ) * (b - c)^6 + (10 : ℝ) * (b - c)^5 * (a - b)^1 + (8 : ℝ) * (b - c)^4 * (a - b)^2 + (2 : ℝ) * (b - c)^3 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 - a*b^3*c^2 - a*b^2*c^3 + 2*b^3*c^3 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / b + b / c + c / a ≥ 3 / 2 + a / (b + c) + b / (a + c) + c / (a + b)) := @solution
#print axioms solution
