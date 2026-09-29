-- Prove2me | solution 1 for WorkbookSource.plus_13348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:41.271876+00:00
-- url     : https://prove2.me/submissions/da95bfb7-2543-428c-8442-f4e05be26fa4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (4 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (a ^ 2 + 4 * b ^ 2 + c ^ 2) + 1 / (a ^ 2 + b ^ 2 + 4 * c ^ 2) ≤ 1 / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 - 4*a^5*b - 4*a^5*c + 13*a^4*b^2 - 4*a^4*b*c + 13*a^4*c^2 - 12*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 - 12*a^3*c^3 + 13*a^2*b^4 - 12*a^2*b^3*c + 60*a^2*b^2*c^2 - 12*a^2*b*c^3 + 13*a^2*c^4 - 4*a*b^5 - 4*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 4*a*b*c^4 - 4*a*c^5 + 2*b^6 - 4*b^5*c + 13*b^4*c^2 - 12*b^3*c^3 + 13*b^2*c^4 - 4*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^2 * (b - a)^4 + (24 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^5 + (50 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (68 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (52 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (22 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (10 : ℝ) * (b - a)^6 + (30 : ℝ) * (b - a)^5 * (c - b)^1 + (45 : ℝ) * (b - a)^4 * (c - b)^2 + (40 : ℝ) * (b - a)^3 * (c - b)^3 + (23 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 - 4*a^5*b - 4*a^5*c + 13*a^4*b^2 - 4*a^4*b*c + 13*a^4*c^2 - 12*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 - 12*a^3*c^3 + 13*a^2*b^4 - 12*a^2*b^3*c + 60*a^2*b^2*c^2 - 12*a^2*b*c^3 + 13*a^2*c^4 - 4*a*b^5 - 4*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 4*a*b*c^4 - 4*a*c^5 + 2*b^6 - 4*b^5*c + 13*b^4*c^2 - 12*b^3*c^3 + 13*b^2*c^4 - 4*b*c^5 + 2*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (4*a^6 + 21*a^4*b^2 + 21*a^4*c^2 - 18*a^4 + 21*a^2*b^4 + 78*a^2*b^2*c^2 - 54*a^2*b^2 + 21*a^2*c^4 - 54*a^2*c^2 + 4*b^6 + 21*b^4*c^2 - 18*b^4 + 21*b^2*c^4 - 54*b^2*c^2 + 4*c^6 - 18*c^4) = (2*a^6 - 4*a^5*b - 4*a^5*c + 13*a^4*b^2 - 4*a^4*b*c + 13*a^4*c^2 - 12*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 - 12*a^3*c^3 + 13*a^2*b^4 - 12*a^2*b^3*c + 60*a^2*b^2*c^2 - 12*a^2*b*c^3 + 13*a^2*c^4 - 4*a*b^5 - 4*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 4*a*b*c^4 - 4*a*c^5 + 2*b^6 - 4*b^5*c + 13*b^4*c^2 - 12*b^3*c^3 + 13*b^2*c^4 - 4*b*c^5 + 2*c^6) := by
    linear_combination (2*a^5 + 2*a^4*b + 2*a^4*c + 6*a^4 + 6*a^3*b^2 + 6*a^3*c^2 + 6*a^2*b^3 + 6*a^2*b^2*c + 18*a^2*b^2 + 6*a^2*b*c^2 + 6*a^2*c^3 + 18*a^2*c^2 + 2*a*b^4 + 6*a*b^2*c^2 + 2*a*c^4 + 2*b^5 + 2*b^4*c + 6*b^4 + 6*b^3*c^2 + 6*b^2*c^3 + 18*b^2*c^2 + 2*b*c^4 + 2*c^5 + 6*c^4) * habc
  have hn : 0 ≤ (4*a^6 + 21*a^4*b^2 + 21*a^4*c^2 - 18*a^4 + 21*a^2*b^4 + 78*a^2*b^2*c^2 - 54*a^2*b^2 + 21*a^2*c^4 - 54*a^2*c^2 + 4*b^6 + 21*b^4*c^2 - 18*b^4 + 21*b^2*c^4 - 54*b^2*c^2 + 4*c^6 - 18*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (4 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (a ^ 2 + 4 * b ^ 2 + c ^ 2) + 1 / (a ^ 2 + b ^ 2 + 4 * c ^ 2) ≤ 1 / 2) := @solution
#print axioms solution
