-- Prove2me | solution 1 for WorkbookSource.plus_3059
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:16:01.108802+00:00
-- url     : https://prove2.me/submissions/d8cd6411-5f2c-4dd7-aafd-2fdc19de3a94

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 * b + 2 * a^2 + 1) / (3 * b + 1) + (b^2 * c + 2 * b^2 + 1) / (3 * c + 1) + (c^2 * a + 2 * c^2 + 1) / (3 * a + 1) ≥ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (19*a^5/27 + 49*a^4*b/27 + 199*a^4*c/27 + 13*a^3*b^2/27 + 160*a^3*b*c/27 + 163*a^3*c^2/27 + 163*a^2*b^3/27 - 67*a^2*b^2*c/3 - 67*a^2*b*c^2/3 + 13*a^2*c^3/27 + 199*a*b^4/27 + 160*a*b^3*c/27 - 67*a*b^2*c^2/3 + 160*a*b*c^3/27 + 49*a*c^4/27 + 19*b^5/27 + 49*b^4*c/27 + 13*b^3*c^2/27 + 163*b^2*c^3/27 + 199*b*c^4/27 + 19*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (184/3 : ℝ) * a^3 * (b - a)^2 + (184/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (184/3 : ℝ) * a^3 * (c - b)^2 + (1150/9 : ℝ) * a^2 * (b - a)^3 + (650/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (604/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (506/9 : ℝ) * a^2 * (c - b)^3 + (2275/27 : ℝ) * a^1 * (b - a)^4 + (5450/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1943/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (2654/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (343/27 : ℝ) * a^1 * (c - b)^4 + (154/9 : ℝ) * (b - a)^5 + (485/9 : ℝ) * (b - a)^4 * (c - b)^1 + (1886/27 : ℝ) * (b - a)^3 * (c - b)^2 + (383/9 : ℝ) * (b - a)^2 * (c - b)^3 + (98/9 : ℝ) * (b - a)^1 * (c - b)^4 + (19/27 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (19*a^5/27 + 49*a^4*b/27 + 199*a^4*c/27 + 13*a^3*b^2/27 + 160*a^3*b*c/27 + 163*a^3*c^2/27 + 163*a^2*b^3/27 - 67*a^2*b^2*c/3 - 67*a^2*b*c^2/3 + 13*a^2*c^3/27 + 199*a*b^4/27 + 160*a*b^3*c/27 - 67*a*b^2*c^2/3 + 160*a*b*c^3/27 + 49*a*c^4/27 + 19*b^5/27 + 49*b^4*c/27 + 13*b^3*c^2/27 + 163*b^2*c^3/27 + 199*b*c^4/27 + 19*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (184/3 : ℝ) * a^3 * (c - a)^2 + (184/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (184/3 : ℝ) * a^3 * (b - c)^2 + (1150/9 : ℝ) * a^2 * (c - a)^3 + (500/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (454/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (506/9 : ℝ) * a^2 * (b - c)^3 + (2275/27 : ℝ) * a^1 * (c - a)^4 + (3650/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (1043/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (1754/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (343/27 : ℝ) * a^1 * (b - c)^4 + (154/9 : ℝ) * (c - a)^5 + (95/3 : ℝ) * (c - a)^4 * (b - c)^1 + (686/27 : ℝ) * (c - a)^3 * (b - c)^2 + (133/9 : ℝ) * (c - a)^2 * (b - c)^3 + (16/3 : ℝ) * (c - a)^1 * (b - c)^4 + (19/27 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (19*a^5/27 + 49*a^4*b/27 + 199*a^4*c/27 + 13*a^3*b^2/27 + 160*a^3*b*c/27 + 163*a^3*c^2/27 + 163*a^2*b^3/27 - 67*a^2*b^2*c/3 - 67*a^2*b*c^2/3 + 13*a^2*c^3/27 + 199*a*b^4/27 + 160*a*b^3*c/27 - 67*a*b^2*c^2/3 + 160*a*b*c^3/27 + 49*a*c^4/27 + 19*b^5/27 + 49*b^4*c/27 + 13*b^3*c^2/27 + 163*b^2*c^3/27 + 199*b*c^4/27 + 19*c^5/27) := by
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
  have he : (9*a^3*b*c + 3*a^3*b + 18*a^3*c + 6*a^3 + 3*a^2*b*c + a^2*b + 6*a^2*c + 2*a^2 + 9*a*b^3*c + 18*a*b^3 + 3*a*b^2*c + 6*a*b^2 + 9*a*b*c^3 + 3*a*b*c^2 - 81*a*b*c - 18*a*b + 3*a*c^3 + a*c^2 - 18*a*c - 3*a + 3*b^3*c + 6*b^3 + b^2*c + 2*b^2 + 18*b*c^3 + 6*b*c^2 - 18*b*c - 3*b + 6*c^3 + 2*c^2 - 3*c) = (19*a^5/27 + 49*a^4*b/27 + 199*a^4*c/27 + 13*a^3*b^2/27 + 160*a^3*b*c/27 + 163*a^3*c^2/27 + 163*a^2*b^3/27 - 67*a^2*b^2*c/3 - 67*a^2*b*c^2/3 + 13*a^2*c^3/27 + 199*a*b^4/27 + 160*a*b^3*c/27 - 67*a*b^2*c^2/3 + 160*a*b*c^3/27 + 49*a*c^4/27 + 19*b^5/27 + 49*b^4*c/27 + 13*b^3*c^2/27 + 163*b^2*c^3/27 + 199*b*c^4/27 + 19*c^5/27) := by
    linear_combination (-19*a^4/27 - 10*a^3*b/9 - 20*a^3*c/3 - 19*a^3/9 + 17*a^2*b^2/27 + 293*a^2*b*c/27 + 16*a^2*b/9 + 17*a^2*c^2/27 + a^2*c/9 - a^2/3 - 20*a*b^3/3 + 293*a*b^2*c/27 + a*b^2/9 + 293*a*b*c^2/27 + 101*a*b*c/3 + 20*a*b/3 - 10*a*c^3/9 + 16*a*c^2/9 + 20*a*c/3 + a - 19*b^4/27 - 10*b^3*c/9 - 19*b^3/9 + 17*b^2*c^2/27 + 16*b^2*c/9 - b^2/3 - 20*b*c^3/3 + b*c^2/9 + 20*b*c/3 + b - 19*c^4/27 - 19*c^3/9 - c^2/3 + c) * hab
  have hn : 0 ≤ (9*a^3*b*c + 3*a^3*b + 18*a^3*c + 6*a^3 + 3*a^2*b*c + a^2*b + 6*a^2*c + 2*a^2 + 9*a*b^3*c + 18*a*b^3 + 3*a*b^2*c + 6*a*b^2 + 9*a*b*c^3 + 3*a*b*c^2 - 81*a*b*c - 18*a*b + 3*a*c^3 + a*c^2 - 18*a*c - 3*a + 3*b^3*c + 6*b^3 + b^2*c + 2*b^2 + 18*b*c^3 + 6*b*c^2 - 18*b*c - 3*b + 6*c^3 + 2*c^2 - 3*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 * b + 2 * a^2 + 1) / (3 * b + 1) + (b^2 * c + 2 * b^2 + 1) / (3 * c + 1) + (c^2 * a + 2 * c^2 + 1) / (3 * a + 1) ≥ 3) := @solution
#print axioms solution
