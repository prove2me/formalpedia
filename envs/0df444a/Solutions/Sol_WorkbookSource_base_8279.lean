-- Prove2me | solution 1 for WorkbookSource.base_8279
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:35.962844+00:00
-- url     : https://prove2.me/submissions/e38e313b-7f88-44a4-afbd-fcae59f0a893

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b^5 + b * c^5 + c * a^5 ≥ a * b * c * (a^2 * b + b^2 * c + c^2 * a)  := by
  have hp : 0 ≤ (a^5*c - a^3*b^2*c - a^2*b*c^3 + a*b^5 - a*b^3*c^2 + b*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (6 : ℝ) * a^4 * (b - a)^2 + (6 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^4 * (c - b)^2 + (15 : ℝ) * a^3 * (b - a)^3 + (28 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (31 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^3 * (c - b)^3 + (14 : ℝ) * a^2 * (b - a)^4 + (39 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (54 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (29 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (5 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (23 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (39 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^1 * (c - b)^5 + (1 : ℝ) * (b - a)^6 + (5 : ℝ) * (b - a)^5 * (c - b)^1 + (10 : ℝ) * (b - a)^4 * (c - b)^2 + (10 : ℝ) * (b - a)^3 * (c - b)^3 + (5 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (6 : ℝ) * a^4 * (c - a)^2 + (6 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (6 : ℝ) * a^4 * (b - c)^2 + (15 : ℝ) * a^3 * (c - a)^3 + (17 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (20 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (9 : ℝ) * a^3 * (b - c)^3 + (14 : ℝ) * a^2 * (c - a)^4 + (17 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (21 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (18 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (5 : ℝ) * a^2 * (b - c)^4 + (6 : ℝ) * a^1 * (c - a)^5 + (7 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (7 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1 : ℝ) * a^1 * (b - c)^5 + (1 : ℝ) * (c - a)^6 + (1 : ℝ) * (c - a)^5 * (b - c)^1 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (6 : ℝ) * c^4 * (a - c)^2 + (6 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (6 : ℝ) * c^4 * (b - a)^2 + (15 : ℝ) * c^3 * (a - c)^3 + (28 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (31 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (9 : ℝ) * c^3 * (b - a)^3 + (14 : ℝ) * c^2 * (a - c)^4 + (39 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (54 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (29 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (5 : ℝ) * c^2 * (b - a)^4 + (6 : ℝ) * c^1 * (a - c)^5 + (23 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (39 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (30 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (10 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (1 : ℝ) * c^1 * (b - a)^5 + (1 : ℝ) * (a - c)^6 + (5 : ℝ) * (a - c)^5 * (b - a)^1 + (10 : ℝ) * (a - c)^4 * (b - a)^2 + (10 : ℝ) * (a - c)^3 * (b - a)^3 + (5 : ℝ) * (a - c)^2 * (b - a)^4 + (1 : ℝ) * (a - c)^1 * (b - a)^5 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (6 : ℝ) * b^4 * (a - b)^2 + (6 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (6 : ℝ) * b^4 * (c - a)^2 + (15 : ℝ) * b^3 * (a - b)^3 + (17 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (20 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (9 : ℝ) * b^3 * (c - a)^3 + (14 : ℝ) * b^2 * (a - b)^4 + (17 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (21 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (18 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (5 : ℝ) * b^2 * (c - a)^4 + (6 : ℝ) * b^1 * (a - b)^5 + (7 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (7 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (9 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (5 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (1 : ℝ) * b^1 * (c - a)^5 + (1 : ℝ) * (a - b)^6 + (1 : ℝ) * (a - b)^5 * (c - a)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (6 : ℝ) * b^4 * (c - b)^2 + (6 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (6 : ℝ) * b^4 * (a - c)^2 + (15 : ℝ) * b^3 * (c - b)^3 + (28 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (31 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (9 : ℝ) * b^3 * (a - c)^3 + (14 : ℝ) * b^2 * (c - b)^4 + (39 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (54 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (29 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (5 : ℝ) * b^2 * (a - c)^4 + (6 : ℝ) * b^1 * (c - b)^5 + (23 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (39 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (30 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (10 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (1 : ℝ) * b^1 * (a - c)^5 + (1 : ℝ) * (c - b)^6 + (5 : ℝ) * (c - b)^5 * (a - c)^1 + (10 : ℝ) * (c - b)^4 * (a - c)^2 + (10 : ℝ) * (c - b)^3 * (a - c)^3 + (5 : ℝ) * (c - b)^2 * (a - c)^4 + (1 : ℝ) * (c - b)^1 * (a - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (6 : ℝ) * c^4 * (b - c)^2 + (6 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (6 : ℝ) * c^4 * (a - b)^2 + (15 : ℝ) * c^3 * (b - c)^3 + (17 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (20 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (9 : ℝ) * c^3 * (a - b)^3 + (14 : ℝ) * c^2 * (b - c)^4 + (17 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (21 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (18 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (5 : ℝ) * c^2 * (a - b)^4 + (6 : ℝ) * c^1 * (b - c)^5 + (7 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (7 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (9 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (5 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (1 : ℝ) * c^1 * (a - b)^5 + (1 : ℝ) * (b - c)^6 + (1 : ℝ) * (b - c)^5 * (a - b)^1 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b^5 + b * c^5 + c * a^5 ≥ a * b * c * (a^2 * b + b^2 * c + c^2 * a)) := @solution
#print axioms solution
