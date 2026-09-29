-- Prove2me | solution 1 for WorkbookSource.base_50971
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:16:05.558833+00:00
-- url     : https://prove2.me/submissions/66a13dd4-5f85-4979-9d3b-40f6ee912eeb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 * (a + b) / (a^2 + a * b + b^2) + b^3 * (b + c) / (b^2 + b * c + c^2) + c^3 * (c + a) / (c^2 + c * a + a^2)) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^6*b^2/9 + 7*a^6*b*c/9 + 7*a^6*c^2/9 + a^5*b^3/3 + 2*a^5*b^2*c/3 + 2*a^5*b*c^2/3 + a^5*c^3/3 + a^4*b^4/9 - 4*a^4*b^3*c/9 - 4*a^4*b^2*c^2/3 - 4*a^4*b*c^3/9 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/9 - 20*a^3*b^3*c^2/9 - 20*a^3*b^2*c^3/9 - 4*a^3*b*c^4/9 + a^3*c^5/3 + 7*a^2*b^6/9 + 2*a^2*b^5*c/3 - 4*a^2*b^4*c^2/3 - 20*a^2*b^3*c^3/9 - 4*a^2*b^2*c^4/3 + 2*a^2*b*c^5/3 + 7*a^2*c^6/9 + 7*a*b^6*c/9 + 2*a*b^5*c^2/3 - 4*a*b^4*c^3/9 - 4*a*b^3*c^4/9 + 2*a*b^2*c^5/3 + 7*a*b*c^6/9 + 7*b^6*c^2/9 + b^5*c^3/3 + b^4*c^4/9 + b^3*c^5/3 + 7*b^2*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^6 * (b - a)^2 + (27 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^6 * (c - b)^2 + (108 : ℝ) * a^5 * (b - a)^3 + (162 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (162 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (54 : ℝ) * a^5 * (c - b)^3 + (178 : ℝ) * a^4 * (b - a)^4 + (356 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (399 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (221 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (43 : ℝ) * a^4 * (c - b)^4 + (156 : ℝ) * a^3 * (b - a)^5 + (390 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (500 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (360 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (126 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * a^3 * (c - b)^5 + (232/3 : ℝ) * a^2 * (b - a)^6 + (232 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (339 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (874/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (138 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (31 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (7/3 : ℝ) * a^2 * (c - b)^6 + (62/3 : ℝ) * a^1 * (b - a)^7 + (217/3 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (359/3 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (355/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (205/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (61/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (7/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (7/3 : ℝ) * (b - a)^8 + (28/3 : ℝ) * (b - a)^7 * (c - b)^1 + (157/9 : ℝ) * (b - a)^6 * (c - b)^2 + (59/3 : ℝ) * (b - a)^5 * (c - b)^3 + (121/9 : ℝ) * (b - a)^4 * (c - b)^4 + (5 : ℝ) * (b - a)^3 * (c - b)^5 + (7/9 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^6*b^2/9 + 7*a^6*b*c/9 + 7*a^6*c^2/9 + a^5*b^3/3 + 2*a^5*b^2*c/3 + 2*a^5*b*c^2/3 + a^5*c^3/3 + a^4*b^4/9 - 4*a^4*b^3*c/9 - 4*a^4*b^2*c^2/3 - 4*a^4*b*c^3/9 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/9 - 20*a^3*b^3*c^2/9 - 20*a^3*b^2*c^3/9 - 4*a^3*b*c^4/9 + a^3*c^5/3 + 7*a^2*b^6/9 + 2*a^2*b^5*c/3 - 4*a^2*b^4*c^2/3 - 20*a^2*b^3*c^3/9 - 4*a^2*b^2*c^4/3 + 2*a^2*b*c^5/3 + 7*a^2*c^6/9 + 7*a*b^6*c/9 + 2*a*b^5*c^2/3 - 4*a*b^4*c^3/9 - 4*a*b^3*c^4/9 + 2*a*b^2*c^5/3 + 7*a*b*c^6/9 + 7*b^6*c^2/9 + b^5*c^3/3 + b^4*c^4/9 + b^3*c^5/3 + 7*b^2*c^6/9) := by
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
  have he : (a^6*b^2 + a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + a^5*c^3 + a^4*b^4 + 2*a^4*b^3*c + 2*a^4*b^2*c^2 - 2*a^4*b^2 + 2*a^4*b*c^3 - 2*a^4*b*c + a^4*c^4 - 2*a^4*c^2 + a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 - 2*a^3*b^3 + 2*a^3*b^2*c^3 - 4*a^3*b^2*c + 2*a^3*b*c^4 - 4*a^3*b*c^2 + a^3*c^5 - 2*a^3*c^3 + a^2*b^6 + 2*a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^4 + 2*a^2*b^3*c^3 - 4*a^2*b^3*c + 2*a^2*b^2*c^4 - 6*a^2*b^2*c^2 + 2*a^2*b*c^5 - 4*a^2*b*c^3 + a^2*c^6 - 2*a^2*c^4 + a*b^6*c + 2*a*b^5*c^2 + 2*a*b^4*c^3 - 2*a*b^4*c + 2*a*b^3*c^4 - 4*a*b^3*c^2 + 2*a*b^2*c^5 - 4*a*b^2*c^3 + a*b*c^6 - 2*a*b*c^4 + b^6*c^2 + b^5*c^3 + b^4*c^4 - 2*b^4*c^2 + b^3*c^5 - 2*b^3*c^3 + b^2*c^6 - 2*b^2*c^4) = (7*a^6*b^2/9 + 7*a^6*b*c/9 + 7*a^6*c^2/9 + a^5*b^3/3 + 2*a^5*b^2*c/3 + 2*a^5*b*c^2/3 + a^5*c^3/3 + a^4*b^4/9 - 4*a^4*b^3*c/9 - 4*a^4*b^2*c^2/3 - 4*a^4*b*c^3/9 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/9 - 20*a^3*b^3*c^2/9 - 20*a^3*b^2*c^3/9 - 4*a^3*b*c^4/9 + a^3*c^5/3 + 7*a^2*b^6/9 + 2*a^2*b^5*c/3 - 4*a^2*b^4*c^2/3 - 20*a^2*b^3*c^3/9 - 4*a^2*b^2*c^4/3 + 2*a^2*b*c^5/3 + 7*a^2*c^6/9 + 7*a*b^6*c/9 + 2*a*b^5*c^2/3 - 4*a*b^4*c^3/9 - 4*a*b^3*c^4/9 + 2*a*b^2*c^5/3 + 7*a*b*c^6/9 + 7*b^6*c^2/9 + b^5*c^3/3 + b^4*c^4/9 + b^3*c^5/3 + 7*b^2*c^6/9) := by
    linear_combination (2*a^5*b^2/9 + 2*a^5*b*c/9 + 2*a^5*c^2/9 + 4*a^4*b^3/9 + 8*a^4*b^2*c/9 + 2*a^4*b^2/3 + 8*a^4*b*c^2/9 + 2*a^4*b*c/3 + 4*a^4*c^3/9 + 2*a^4*c^2/3 + 4*a^3*b^4/9 + 10*a^3*b^3*c/9 + 2*a^3*b^3/3 + 14*a^3*b^2*c^2/9 + 4*a^3*b^2*c/3 + 10*a^3*b*c^3/9 + 4*a^3*b*c^2/3 + 4*a^3*c^4/9 + 2*a^3*c^3/3 + 2*a^2*b^5/9 + 8*a^2*b^4*c/9 + 2*a^2*b^4/3 + 14*a^2*b^3*c^2/9 + 4*a^2*b^3*c/3 + 14*a^2*b^2*c^3/9 + 2*a^2*b^2*c^2 + 8*a^2*b*c^4/9 + 4*a^2*b*c^3/3 + 2*a^2*c^5/9 + 2*a^2*c^4/3 + 2*a*b^5*c/9 + 8*a*b^4*c^2/9 + 2*a*b^4*c/3 + 10*a*b^3*c^3/9 + 4*a*b^3*c^2/3 + 8*a*b^2*c^4/9 + 4*a*b^2*c^3/3 + 2*a*b*c^5/9 + 2*a*b*c^4/3 + 2*b^5*c^2/9 + 4*b^4*c^3/9 + 2*b^4*c^2/3 + 4*b^3*c^4/9 + 2*b^3*c^3/3 + 2*b^2*c^5/9 + 2*b^2*c^4/3) * hab
  have hn : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + a^5*c^3 + a^4*b^4 + 2*a^4*b^3*c + 2*a^4*b^2*c^2 - 2*a^4*b^2 + 2*a^4*b*c^3 - 2*a^4*b*c + a^4*c^4 - 2*a^4*c^2 + a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 - 2*a^3*b^3 + 2*a^3*b^2*c^3 - 4*a^3*b^2*c + 2*a^3*b*c^4 - 4*a^3*b*c^2 + a^3*c^5 - 2*a^3*c^3 + a^2*b^6 + 2*a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^4 + 2*a^2*b^3*c^3 - 4*a^2*b^3*c + 2*a^2*b^2*c^4 - 6*a^2*b^2*c^2 + 2*a^2*b*c^5 - 4*a^2*b*c^3 + a^2*c^6 - 2*a^2*c^4 + a*b^6*c + 2*a*b^5*c^2 + 2*a*b^4*c^3 - 2*a*b^4*c + 2*a*b^3*c^4 - 4*a*b^3*c^2 + 2*a*b^2*c^5 - 4*a*b^2*c^3 + a*b*c^6 - 2*a*b*c^4 + b^6*c^2 + b^5*c^3 + b^4*c^4 - 2*b^4*c^2 + b^3*c^5 - 2*b^3*c^3 + b^2*c^6 - 2*b^2*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^3 * (a + b) / (a^2 + a * b + b^2) + b^3 * (b + c) / (b^2 + b * c + c^2) + c^3 * (c + a) / (c^2 + c * a + a^2)) ≥ 2) := @solution
#print axioms solution
