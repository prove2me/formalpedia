-- Prove2me | solution 1 for WorkbookSource.plus_73744
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:25.513637+00:00
-- url     : https://prove2.me/submissions/3ba46bdc-26b9-46ea-90bb-476bf4545139

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / ((a + b) ^ 2 + b * c) + b * c / ((b + c) ^ 2 + c * a) + c * a / ((c + a) ^ 2 + a * b)) ≤ 3 / 5   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5*c + 3*a^4*b^2 + 5*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 2*a^3*b^2*c - 9*a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 9*a^2*b^3*c - 24*a^2*b^2*c^2 - 2*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 + 5*a*b^4*c - 2*a*b^3*c^2 - 9*a*b^2*c^3 + 5*a*b*c^4 + 3*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4 + 3*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (65 : ℝ) * a^4 * (b - a)^2 + (65 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (65 : ℝ) * a^4 * (c - b)^2 + (185 : ℝ) * a^3 * (b - a)^3 + (293 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (258 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (75 : ℝ) * a^3 * (c - b)^3 + (192 : ℝ) * a^2 * (b - a)^4 + (415 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (405 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (182 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (27 : ℝ) * a^2 * (c - b)^4 + (86 : ℝ) * a^1 * (b - a)^5 + (239 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (277 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (161 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (43 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * a^1 * (c - b)^5 + (14 : ℝ) * (b - a)^6 + (49 : ℝ) * (b - a)^5 * (c - b)^1 + (69 : ℝ) * (b - a)^4 * (c - b)^2 + (50 : ℝ) * (b - a)^3 * (c - b)^3 + (19 : ℝ) * (b - a)^2 * (c - b)^4 + (3 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^5*c + 3*a^4*b^2 + 5*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 2*a^3*b^2*c - 9*a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 9*a^2*b^3*c - 24*a^2*b^2*c^2 - 2*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 + 5*a*b^4*c - 2*a*b^3*c^2 - 9*a*b^2*c^3 + 5*a*b*c^4 + 3*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4 + 3*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (65 : ℝ) * a^4 * (c - a)^2 + (65 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (65 : ℝ) * a^4 * (b - c)^2 + (185 : ℝ) * a^3 * (c - a)^3 + (262 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (227 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (75 : ℝ) * a^3 * (b - c)^3 + (192 : ℝ) * a^2 * (c - a)^4 + (353 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (312 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (151 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (27 : ℝ) * a^2 * (b - c)^4 + (86 : ℝ) * a^1 * (c - a)^5 + (191 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (181 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (96 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (26 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * a^1 * (b - c)^5 + (14 : ℝ) * (c - a)^6 + (35 : ℝ) * (c - a)^5 * (b - c)^1 + (34 : ℝ) * (c - a)^4 * (b - c)^2 + (16 : ℝ) * (c - a)^3 * (b - c)^3 + (3 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5*c + 3*a^4*b^2 + 5*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 2*a^3*b^2*c - 9*a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 9*a^2*b^3*c - 24*a^2*b^2*c^2 - 2*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 + 5*a*b^4*c - 2*a*b^3*c^2 - 9*a*b^2*c^3 + 5*a*b*c^4 + 3*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4 + 3*b*c^5) := by
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
  have hn : 0 ≤ (3*a^5*c + 3*a^4*b^2 + 5*a^4*b*c + 4*a^4*c^2 + 4*a^3*b^3 - 2*a^3*b^2*c - 9*a^3*b*c^2 + 4*a^3*c^3 + 4*a^2*b^4 - 9*a^2*b^3*c - 24*a^2*b^2*c^2 - 2*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 + 5*a*b^4*c - 2*a*b^3*c^2 - 9*a*b^2*c^3 + 5*a*b*c^4 + 3*b^4*c^2 + 4*b^3*c^3 + 4*b^2*c^4 + 3*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / ((a + b) ^ 2 + b * c) + b * c / ((b + c) ^ 2 + c * a) + c * a / ((c + a) ^ 2 + a * b)) ≤ 3 / 5) := @solution
#print axioms solution
