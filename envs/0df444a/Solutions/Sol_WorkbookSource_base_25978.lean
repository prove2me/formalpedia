-- Prove2me | solution 1 for WorkbookSource.base_25978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:07:50.236023+00:00
-- url     : https://prove2.me/submissions/2d1d3464-3248-4dc4-9d39-585c11e7b7fe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) ≥ 9 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b*c + 2*a^4*c^2 + 4*a^3*b^3 - 5*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - 5*a^2*b*c^3 + 4*a*b^4*c - 5*a*b^3*c^2 - 3*a*b^2*c^3 + 4*a*b*c^4 + 4*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (72 : ℝ) * a^3 * (b - a)^3 + (117 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (93 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (24 : ℝ) * a^3 * (c - b)^3 + (78 : ℝ) * a^2 * (b - a)^4 + (174 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (153 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (57 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (36 : ℝ) * a^1 * (b - a)^5 + (101 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (106 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (49 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (b - a)^6 + (20 : ℝ) * (b - a)^5 * (c - b)^1 + (24 : ℝ) * (b - a)^4 * (c - b)^2 + (12 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*b*c + 2*a^4*c^2 + 4*a^3*b^3 - 5*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - 5*a^2*b*c^3 + 4*a*b^4*c - 5*a*b^3*c^2 - 3*a*b^2*c^3 + 4*a*b*c^4 + 4*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (c - a)^2 + (24 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^4 * (b - c)^2 + (72 : ℝ) * a^3 * (c - a)^3 + (99 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (75 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (24 : ℝ) * a^3 * (b - c)^3 + (78 : ℝ) * a^2 * (c - a)^4 + (138 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (99 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (39 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^2 * (b - c)^4 + (36 : ℝ) * a^1 * (c - a)^5 + (79 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (62 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (23 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * (c - a)^6 + (16 : ℝ) * (c - a)^5 * (b - c)^1 + (14 : ℝ) * (c - a)^4 * (b - c)^2 + (4 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b*c + 2*a^4*c^2 + 4*a^3*b^3 - 5*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - 5*a^2*b*c^3 + 4*a*b^4*c - 5*a*b^3*c^2 - 3*a*b^2*c^3 + 4*a*b*c^4 + 4*b^3*c^3 + 2*b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (4*a^4*b*c + 2*a^4*c^2 + 4*a^3*b^3 - 5*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - 5*a^2*b*c^3 + 4*a*b^4*c - 5*a*b^3*c^2 - 3*a*b^2*c^3 + 4*a*b*c^4 + 4*b^3*c^3 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) * (a / (a + b) + b / (b + c) + c / (c + a)) ≥ 9 / 2) := @solution
#print axioms solution
