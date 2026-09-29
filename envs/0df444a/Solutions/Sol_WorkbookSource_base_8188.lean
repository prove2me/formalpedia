-- Prove2me | solution 1 for WorkbookSource.base_8188
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:35:55.971531+00:00
-- url     : https://prove2.me/submissions/16bbf8e9-f78d-4eea-b623-c6c6c1a880f3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : 4 * (3 * (3 - a) * (3 - b) * (3 - c)) / a ^ 2 + 4 * (3 * (3 - b) * (3 - c) * (3 - a)) / b ^ 2 + 4 * (3 * (3 - c) * (3 - a) * (3 - b)) / c ^ 2 ≤ 7 / 2 * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2/2 + a^6*c^2/2 - a^4*b^4 + 11*a^4*b^2*c^2/2 - a^4*c^4 + a^2*b^6/2 + 11*a^2*b^4*c^2/2 + 11*a^2*b^2*c^4/2 + a^2*c^6/2 + b^6*c^2/2 - b^4*c^4 + b^2*c^6/2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (33/2 : ℝ) * a^8 + (88 : ℝ) * a^7 * (b - a)^1 + (44 : ℝ) * a^7 * (c - b)^1 + (202 : ℝ) * a^6 * (b - a)^2 + (202 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (48 : ℝ) * a^6 * (c - b)^2 + (254 : ℝ) * a^5 * (b - a)^3 + (381 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (195 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (34 : ℝ) * a^5 * (c - b)^3 + (367/2 : ℝ) * a^4 * (b - a)^4 + (367 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (611/2 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (122 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (37/2 : ℝ) * a^4 * (c - b)^4 + (72 : ℝ) * a^3 * (b - a)^5 + (180 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (224 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (156 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (52 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (12 : ℝ) * a^2 * (b - a)^6 + (36 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (76 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (92 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (52 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (12 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (26 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (9 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^6 * (c - b)^2 + (6 : ℝ) * (b - a)^5 * (c - b)^3 + (13/2 : ℝ) * (b - a)^4 * (c - b)^4 + (3 : ℝ) * (b - a)^3 * (c - b)^5 + (1/2 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2/2 + a^6*c^2/2 - a^4*b^4 + 11*a^4*b^2*c^2/2 - a^4*c^4 + a^2*b^6/2 + 11*a^2*b^4*c^2/2 + 11*a^2*b^2*c^4/2 + a^2*c^6/2 + b^6*c^2/2 - b^4*c^4 + b^2*c^6/2) := by
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
  have he : (7*a^4*b^2*c^2 + 24*a^3*b^3*c - 72*a^3*b^3 - 72*a^3*b^2*c + 216*a^3*b^2 + 24*a^3*b*c^3 - 72*a^3*b*c^2 - 72*a^3*c^3 + 216*a^3*c^2 + 7*a^2*b^4*c^2 - 72*a^2*b^3*c + 216*a^2*b^3 + 7*a^2*b^2*c^4 + 216*a^2*b^2*c - 648*a^2*b^2 - 72*a^2*b*c^3 + 216*a^2*b*c^2 + 216*a^2*c^3 - 648*a^2*c^2 + 24*a*b^3*c^3 - 72*a*b^3*c^2 - 72*a*b^2*c^3 + 216*a*b^2*c^2 - 72*b^3*c^3 + 216*b^3*c^2 + 216*b^2*c^3 - 648*b^2*c^2) = (a^6*b^2/2 + a^6*c^2/2 - a^4*b^4 + 11*a^4*b^2*c^2/2 - a^4*c^4 + a^2*b^6/2 + 11*a^2*b^4*c^2/2 + 11*a^2*b^2*c^4/2 + a^2*c^6/2 + b^6*c^2/2 - b^4*c^4 + b^2*c^6/2) := by
    linear_combination (-a^5*b^2/2 - a^5*c^2/2 + a^4*b^3/2 + a^4*b^2*c/2 - 3*a^4*b^2 + a^4*b*c^2/2 + a^4*c^3/2 - 3*a^4*c^2 + a^3*b^4/2 - a^3*b^3*c + 6*a^3*b^3 + a^3*b^2*c^2/2 + 6*a^3*b^2*c - 18*a^3*b^2 - a^3*b*c^3 + 6*a^3*b*c^2 + a^3*c^4/2 + 6*a^3*c^3 - 18*a^3*c^2 - a^2*b^5/2 + a^2*b^4*c/2 - 3*a^2*b^4 + a^2*b^3*c^2/2 + 6*a^2*b^3*c - 18*a^2*b^3 + a^2*b^2*c^3/2 - 9*a^2*b^2*c^2 - 18*a^2*b^2*c + 108*a^2*b^2 + a^2*b*c^4/2 + 6*a^2*b*c^3 - 18*a^2*b*c^2 - a^2*c^5/2 - 3*a^2*c^4 - 18*a^2*c^3 + 108*a^2*c^2 + a*b^4*c^2/2 - a*b^3*c^3 + 6*a*b^3*c^2 + a*b^2*c^4/2 + 6*a*b^2*c^3 - 18*a*b^2*c^2 - b^5*c^2/2 + b^4*c^3/2 - 3*b^4*c^2 + b^3*c^4/2 + 6*b^3*c^3 - 18*b^3*c^2 - b^2*c^5/2 - 3*b^2*c^4 - 18*b^2*c^3 + 108*b^2*c^2) * habc
  have hn : 0 ≤ (7*a^4*b^2*c^2 + 24*a^3*b^3*c - 72*a^3*b^3 - 72*a^3*b^2*c + 216*a^3*b^2 + 24*a^3*b*c^3 - 72*a^3*b*c^2 - 72*a^3*c^3 + 216*a^3*c^2 + 7*a^2*b^4*c^2 - 72*a^2*b^3*c + 216*a^2*b^3 + 7*a^2*b^2*c^4 + 216*a^2*b^2*c - 648*a^2*b^2 - 72*a^2*b*c^3 + 216*a^2*b*c^2 + 216*a^2*c^3 - 648*a^2*c^2 + 24*a*b^3*c^3 - 72*a*b^3*c^2 - 72*a*b^2*c^3 + 216*a*b^2*c^2 - 72*b^3*c^3 + 216*b^3*c^2 + 216*b^2*c^3 - 648*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6), 4 * (3 * (3 - a) * (3 - b) * (3 - c)) / a ^ 2 + 4 * (3 * (3 - b) * (3 - c) * (3 - a)) / b ^ 2 + 4 * (3 * (3 - c) * (3 - a) * (3 - b)) / c ^ 2 ≤ 7 / 2 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
