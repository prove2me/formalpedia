-- Prove2me | solution 1 for WorkbookSource.base_17948
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:28:27.863172+00:00
-- url     : https://prove2.me/submissions/f0b7dab2-e1de-4897-bd9b-eff9a6ae7860

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + 1) + b * c / (2 * a ^ 2 + b * c + 1) + c * a / (2 * b ^ 2 + c * a + 1)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (1 + a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b*c + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 2*a^5*b + 4*a^5*c^3 + 2*a^5*c - 4*a^4*b^4 - 2*a^4*b^3*c + 5*a^4*b^2*c^2 + 2*a^4*b^2 - 2*a^4*b*c^3 - 7*a^4*b*c - 4*a^4*c^4 + 2*a^4*c^2 + 2*a^4 + 4*a^3*b^5 - 2*a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b^2*c - 2*a^3*b*c^4 - a^3*b*c^2 - a^3*b + 4*a^3*c^5 - a^3*c - 4*a^2*b^5*c + 5*a^2*b^4*c^2 + 2*a^2*b^4 + a^2*b^3*c^3 - a^2*b^3*c + 5*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + 3*a^2*b^2 - 4*a^2*b*c^5 - a^2*b*c^3 - 3*a^2*b*c + 2*a^2*c^4 + 3*a^2*c^2 + a^2 + 2*a*b^6*c - 4*a*b^5*c^2 + 2*a*b^5 - 2*a*b^4*c^3 - 7*a*b^4*c - 2*a*b^3*c^4 - a*b^3*c^2 - a*b^3 - 4*a*b^2*c^5 - a*b^2*c^3 - 3*a*b^2*c + 2*a*b*c^6 - 7*a*b*c^4 - 3*a*b*c^2 - a*b + 2*a*c^5 - a*c^3 - a*c + 4*b^5*c^3 + 2*b^5*c - 4*b^4*c^4 + 2*b^4*c^2 + 2*b^4 + 4*b^3*c^5 - b^3*c + 2*b^2*c^4 + 3*b^2*c^2 + b^2 + 2*b*c^5 - b*c^3 - b*c + 2*c^4 + c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^6 * (b - a)^2 + (9 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^6 * (c - b)^2 + (36 : ℝ) * a^5 * (b - a)^3 + (54 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (54 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^5 * (c - b)^3 + (68 : ℝ) * a^4 * (b - a)^4 + (136 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (159 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (21 : ℝ) * a^4 * (b - a)^2 + (91 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (21 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (23 : ℝ) * a^4 * (c - b)^4 + (21 : ℝ) * a^4 * (c - b)^2 + (80 : ℝ) * a^3 * (b - a)^5 + (200 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (264 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (58 : ℝ) * a^3 * (b - a)^3 + (196 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (87 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (76 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (81 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^5 + (26 : ℝ) * a^3 * (c - b)^3 + (59 : ℝ) * a^2 * (b - a)^6 + (177 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (258 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (65 : ℝ) * a^2 * (b - a)^4 + (221 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (130 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (138 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (9 : ℝ) * a^2 * (b - a)^2 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (73 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^2 * (c - b)^6 + (17 : ℝ) * a^2 * (c - b)^4 + (9 : ℝ) * a^2 * (c - b)^2 + (24 : ℝ) * a^1 * (b - a)^7 + (84 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (136 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (36 : ℝ) * a^1 * (b - a)^5 + (130 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (90 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (72 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (110 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (12 : ℝ) * a^1 * (b - a)^3 + (20 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (75 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^1 * (c - b)^5 + (6 : ℝ) * a^1 * (c - b)^3 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (28 : ℝ) * (b - a)^6 * (c - b)^2 + (8 : ℝ) * (b - a)^6 + (28 : ℝ) * (b - a)^5 * (c - b)^3 + (24 : ℝ) * (b - a)^5 * (c - b)^1 + (16 : ℝ) * (b - a)^4 * (c - b)^4 + (34 : ℝ) * (b - a)^4 * (c - b)^2 + (5 : ℝ) * (b - a)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^5 + (28 : ℝ) * (b - a)^3 * (c - b)^3 + (10 : ℝ) * (b - a)^3 * (c - b)^1 + (12 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^2 * (c - b)^2 + (1 : ℝ) * (b - a)^2 + (2 : ℝ) * (b - a)^1 * (c - b)^5 + (7 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^1 + (2 : ℝ) * (c - b)^4 + (1 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b*c + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 2*a^5*b + 4*a^5*c^3 + 2*a^5*c - 4*a^4*b^4 - 2*a^4*b^3*c + 5*a^4*b^2*c^2 + 2*a^4*b^2 - 2*a^4*b*c^3 - 7*a^4*b*c - 4*a^4*c^4 + 2*a^4*c^2 + 2*a^4 + 4*a^3*b^5 - 2*a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b^2*c - 2*a^3*b*c^4 - a^3*b*c^2 - a^3*b + 4*a^3*c^5 - a^3*c - 4*a^2*b^5*c + 5*a^2*b^4*c^2 + 2*a^2*b^4 + a^2*b^3*c^3 - a^2*b^3*c + 5*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + 3*a^2*b^2 - 4*a^2*b*c^5 - a^2*b*c^3 - 3*a^2*b*c + 2*a^2*c^4 + 3*a^2*c^2 + a^2 + 2*a*b^6*c - 4*a*b^5*c^2 + 2*a*b^5 - 2*a*b^4*c^3 - 7*a*b^4*c - 2*a*b^3*c^4 - a*b^3*c^2 - a*b^3 - 4*a*b^2*c^5 - a*b^2*c^3 - 3*a*b^2*c + 2*a*b*c^6 - 7*a*b*c^4 - 3*a*b*c^2 - a*b + 2*a*c^5 - a*c^3 - a*c + 4*b^5*c^3 + 2*b^5*c - 4*b^4*c^4 + 2*b^4*c^2 + 2*b^4 + 4*b^3*c^5 - b^3*c + 2*b^2*c^4 + 3*b^2*c^2 + b^2 + 2*b*c^5 - b*c^3 - b*c + 2*c^4 + c^2) := by
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
  have hn : 0 ≤ (2*a^6*b*c + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 2*a^5*b + 4*a^5*c^3 + 2*a^5*c - 4*a^4*b^4 - 2*a^4*b^3*c + 5*a^4*b^2*c^2 + 2*a^4*b^2 - 2*a^4*b*c^3 - 7*a^4*b*c - 4*a^4*c^4 + 2*a^4*c^2 + 2*a^4 + 4*a^3*b^5 - 2*a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b^2*c - 2*a^3*b*c^4 - a^3*b*c^2 - a^3*b + 4*a^3*c^5 - a^3*c - 4*a^2*b^5*c + 5*a^2*b^4*c^2 + 2*a^2*b^4 + a^2*b^3*c^3 - a^2*b^3*c + 5*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + 3*a^2*b^2 - 4*a^2*b*c^5 - a^2*b*c^3 - 3*a^2*b*c + 2*a^2*c^4 + 3*a^2*c^2 + a^2 + 2*a*b^6*c - 4*a*b^5*c^2 + 2*a*b^5 - 2*a*b^4*c^3 - 7*a*b^4*c - 2*a*b^3*c^4 - a*b^3*c^2 - a*b^3 - 4*a*b^2*c^5 - a*b^2*c^3 - 3*a*b^2*c + 2*a*b*c^6 - 7*a*b*c^4 - 3*a*b*c^2 - a*b + 2*a*c^5 - a*c^3 - a*c + 4*b^5*c^3 + 2*b^5*c - 4*b^4*c^4 + 2*b^4*c^2 + 2*b^4 + 4*b^3*c^5 - b^3*c + 2*b^2*c^4 + 3*b^2*c^2 + b^2 + 2*b*c^5 - b*c^3 - b*c + 2*c^4 + c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (2 * c ^ 2 + a * b + 1) + b * c / (2 * a ^ 2 + b * c + 1) + c * a / (2 * b ^ 2 + c * a + 1)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (1 + a * b + b * c + a * c)) := @solution
#print axioms solution
