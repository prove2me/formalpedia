-- Prove2me | solution 1 for WorkbookSource.base_51471
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:42:57.187408+00:00
-- url     : https://prove2.me/submissions/95d6b0d2-0ade-4dfc-8a4d-ba0d8a3e1d1a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 9 / 2 - (a / (a + b) + b / (b + c) + c / (c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (b - a)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (48 : ℝ) * a^3 * (b - a)^3 + (79 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (63 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (52 : ℝ) * a^2 * (b - a)^4 + (118 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (39 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (69 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (74 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (35 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (14 : ℝ) * (b - a)^5 * (c - b)^1 + (18 : ℝ) * (b - a)^4 * (c - b)^2 + (10 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (c - a)^2 + (16 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^4 * (b - c)^2 + (48 : ℝ) * a^3 * (c - a)^3 + (65 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (49 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (16 : ℝ) * a^3 * (b - c)^3 + (52 : ℝ) * a^2 * (c - a)^4 + (90 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (63 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (25 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (24 : ℝ) * a^1 * (c - a)^5 + (51 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (38 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (13 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (10 : ℝ) * (c - a)^5 * (b - c)^1 + (8 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ≥ 9 / 2 - (a / (a + b) + b / (b + c) + c / (c + a))) := @solution
#print axioms solution
