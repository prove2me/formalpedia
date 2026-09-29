-- Prove2me | solution 1 for WorkbookSource.base_7483
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:33.058748+00:00
-- url     : https://prove2.me/submissions/da9442bb-6f37-4cb0-ace3-608ec62840a6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥ a * b * c * (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c)  := by
  have hp : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 - a*b^3*c^2 - a*b^2*c^3 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (38 : ℝ) * a^3 * (b - a)^3 + (57 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (39 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^3 * (c - b)^3 + (44 : ℝ) * a^2 * (b - a)^4 + (88 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (19 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (22 : ℝ) * a^1 * (b - a)^5 + (55 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (48 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (17 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * a^4 * (c - a)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^4 * (b - c)^2 + (38 : ℝ) * a^3 * (c - a)^3 + (57 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (39 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (10 : ℝ) * a^3 * (b - c)^3 + (44 : ℝ) * a^2 * (c - a)^4 + (88 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (63 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (19 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (22 : ℝ) * a^1 * (c - a)^5 + (55 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (48 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (17 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (12 : ℝ) * (c - a)^5 * (b - c)^1 + (13 : ℝ) * (c - a)^4 * (b - c)^2 + (6 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^4 * (a - c)^2 + (12 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (12 : ℝ) * c^4 * (b - a)^2 + (38 : ℝ) * c^3 * (a - c)^3 + (57 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (39 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (10 : ℝ) * c^3 * (b - a)^3 + (44 : ℝ) * c^2 * (a - c)^4 + (88 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (63 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (19 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (2 : ℝ) * c^2 * (b - a)^4 + (22 : ℝ) * c^1 * (a - c)^5 + (55 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (48 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (17 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (2 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (4 : ℝ) * (a - c)^6 + (12 : ℝ) * (a - c)^5 * (b - a)^1 + (13 : ℝ) * (a - c)^4 * (b - a)^2 + (6 : ℝ) * (a - c)^3 * (b - a)^3 + (1 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * b^4 * (a - b)^2 + (12 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (12 : ℝ) * b^4 * (c - a)^2 + (38 : ℝ) * b^3 * (a - b)^3 + (57 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (39 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (10 : ℝ) * b^3 * (c - a)^3 + (44 : ℝ) * b^2 * (a - b)^4 + (88 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (63 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (19 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (2 : ℝ) * b^2 * (c - a)^4 + (22 : ℝ) * b^1 * (a - b)^5 + (55 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (48 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (17 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (2 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (4 : ℝ) * (a - b)^6 + (12 : ℝ) * (a - b)^5 * (c - a)^1 + (13 : ℝ) * (a - b)^4 * (c - a)^2 + (6 : ℝ) * (a - b)^3 * (c - a)^3 + (1 : ℝ) * (a - b)^2 * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * b^4 * (c - b)^2 + (12 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (12 : ℝ) * b^4 * (a - c)^2 + (38 : ℝ) * b^3 * (c - b)^3 + (57 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (39 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (10 : ℝ) * b^3 * (a - c)^3 + (44 : ℝ) * b^2 * (c - b)^4 + (88 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (63 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (19 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (2 : ℝ) * b^2 * (a - c)^4 + (22 : ℝ) * b^1 * (c - b)^5 + (55 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (48 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (17 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * (c - b)^6 + (12 : ℝ) * (c - b)^5 * (a - c)^1 + (13 : ℝ) * (c - b)^4 * (a - c)^2 + (6 : ℝ) * (c - b)^3 * (a - c)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^4 * (b - c)^2 + (12 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (12 : ℝ) * c^4 * (a - b)^2 + (38 : ℝ) * c^3 * (b - c)^3 + (57 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (39 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (10 : ℝ) * c^3 * (a - b)^3 + (44 : ℝ) * c^2 * (b - c)^4 + (88 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (63 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (19 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (2 : ℝ) * c^2 * (a - b)^4 + (22 : ℝ) * c^1 * (b - c)^5 + (55 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (48 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (17 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (2 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (4 : ℝ) * (b - c)^6 + (12 : ℝ) * (b - c)^5 * (a - b)^1 + (13 : ℝ) * (b - c)^4 * (a - b)^2 + (6 : ℝ) * (b - c)^3 * (a - b)^3 + (1 : ℝ) * (b - c)^2 * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥ a * b * c * (2 * a + b + c) * (a + 2 * b + c) * (a + b + 2 * c)) := @solution
#print axioms solution
