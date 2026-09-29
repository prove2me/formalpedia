-- Prove2me | solution 1 for WorkbookSource.base_471
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:41.884194+00:00
-- url     : https://prove2.me/submissions/a6101c57-ad3b-4cb6-ac3c-775b0b6239a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a - b) / (a ^ 2 + b ^ 2) + b * (b - c) / (b ^ 2 + c ^ 2) + c * (c - a) / (c ^ 2 + a ^ 2)) ≥ 0  := by
  have hp : 0 ≤ (2*a^4*b^2 - a^4*b*c + a^4*c^2 - a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - a^3*c^3 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - a*b*c^4 + 2*b^4*c^2 - b^3*c^3 + b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (12 : ℝ) * a^3 * (b - a)^3 + (14 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (10 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (14 : ℝ) * a^2 * (b - a)^4 + (20 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (12 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (10 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (b - a)^6 + (5 : ℝ) * (b - a)^5 * (c - b)^1 + (5 : ℝ) * (b - a)^4 * (c - b)^2 + (3 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * a^4 * (c - a)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^4 * (b - c)^2 + (12 : ℝ) * a^3 * (c - a)^3 + (22 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (18 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^3 * (b - c)^3 + (14 : ℝ) * a^2 * (c - a)^4 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (36 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (14 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (8 : ℝ) * a^1 * (c - a)^5 + (25 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (30 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (16 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (c - a)^6 + (7 : ℝ) * (c - a)^5 * (b - c)^1 + (10 : ℝ) * (c - a)^4 * (b - c)^2 + (7 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * c^4 * (a - c)^2 + (4 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (4 : ℝ) * c^4 * (b - a)^2 + (12 : ℝ) * c^3 * (a - c)^3 + (14 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (10 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (4 : ℝ) * c^3 * (b - a)^3 + (14 : ℝ) * c^2 * (a - c)^4 + (20 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (12 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (6 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (2 : ℝ) * c^2 * (b - a)^4 + (8 : ℝ) * c^1 * (a - c)^5 + (15 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (10 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (4 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (1 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (2 : ℝ) * (a - c)^6 + (5 : ℝ) * (a - c)^5 * (b - a)^1 + (5 : ℝ) * (a - c)^4 * (b - a)^2 + (3 : ℝ) * (a - c)^3 * (b - a)^3 + (1 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * b^4 * (a - b)^2 + (4 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (4 : ℝ) * b^4 * (c - a)^2 + (12 : ℝ) * b^3 * (a - b)^3 + (22 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (18 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (4 : ℝ) * b^3 * (c - a)^3 + (14 : ℝ) * b^2 * (a - b)^4 + (36 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (36 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (14 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (2 : ℝ) * b^2 * (c - a)^4 + (8 : ℝ) * b^1 * (a - b)^5 + (25 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (30 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (16 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (3 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (2 : ℝ) * (a - b)^6 + (7 : ℝ) * (a - b)^5 * (c - a)^1 + (10 : ℝ) * (a - b)^4 * (c - a)^2 + (7 : ℝ) * (a - b)^3 * (c - a)^3 + (2 : ℝ) * (a - b)^2 * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * b^4 * (c - b)^2 + (4 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^4 * (a - c)^2 + (12 : ℝ) * b^3 * (c - b)^3 + (14 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (10 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (4 : ℝ) * b^3 * (a - c)^3 + (14 : ℝ) * b^2 * (c - b)^4 + (20 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (12 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (6 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (2 : ℝ) * b^2 * (a - c)^4 + (8 : ℝ) * b^1 * (c - b)^5 + (15 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (10 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (4 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (1 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (2 : ℝ) * (c - b)^6 + (5 : ℝ) * (c - b)^5 * (a - c)^1 + (5 : ℝ) * (c - b)^4 * (a - c)^2 + (3 : ℝ) * (c - b)^3 * (a - c)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * c^4 * (b - c)^2 + (4 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (4 : ℝ) * c^4 * (a - b)^2 + (12 : ℝ) * c^3 * (b - c)^3 + (22 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (18 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (4 : ℝ) * c^3 * (a - b)^3 + (14 : ℝ) * c^2 * (b - c)^4 + (36 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (36 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (14 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (2 : ℝ) * c^2 * (a - b)^4 + (8 : ℝ) * c^1 * (b - c)^5 + (25 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (30 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (16 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (3 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (2 : ℝ) * (b - c)^6 + (7 : ℝ) * (b - c)^5 * (a - b)^1 + (10 : ℝ) * (b - c)^4 * (a - b)^2 + (7 : ℝ) * (b - c)^3 * (a - b)^3 + (2 : ℝ) * (b - c)^2 * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (2*a^4*b^2 - a^4*b*c + a^4*c^2 - a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - a^3*c^3 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - a*b*c^4 + 2*b^4*c^2 - b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (a - b) / (a ^ 2 + b ^ 2) + b * (b - c) / (b ^ 2 + c ^ 2) + c * (c - a) / (c ^ 2 + a ^ 2)) ≥ 0) := @solution
#print axioms solution
