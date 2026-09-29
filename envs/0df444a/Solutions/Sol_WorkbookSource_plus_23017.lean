-- Prove2me | solution 1 for WorkbookSource.plus_23017
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:48.978238+00:00
-- url     : https://prove2.me/submissions/31708dca-5d7c-4f2e-9287-619fcde88e40

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (a / (a + 1) + b / (b + 1) + c / (c + 1)) ≥ (3 * (1 + a * b * c)) / 4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^5*b/81 + 5*a^5*c/81 + 20*a^4*b^2/81 + 4*a^4*b*c/9 + 20*a^4*c^2/81 + 10*a^3*b^3/27 + 2*a^3*b^2*c/81 + 2*a^3*b*c^2/81 + 10*a^3*c^3/27 + 20*a^2*b^4/81 + 2*a^2*b^3*c/81 - 40*a^2*b^2*c^2/9 + 2*a^2*b*c^3/81 + 20*a^2*c^4/81 + 5*a*b^5/81 + 4*a*b^4*c/9 + 2*a*b^3*c^2/81 + 2*a*b^2*c^3/81 + 4*a*b*c^4/9 + 5*a*c^5/81 + 5*b^5*c/81 + 20*b^4*c^2/81 + 10*b^3*c^3/27 + 20*b^2*c^4/81 + 5*b*c^5/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (140/9 : ℝ) * a^3 * (b - a)^3 + (70/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (58/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (52/9 : ℝ) * a^3 * (c - b)^3 + (146/9 : ℝ) * a^2 * (b - a)^4 + (292/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (28 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (106/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14/9 : ℝ) * a^2 * (c - b)^4 + (566/81 : ℝ) * a^1 * (b - a)^5 + (1415/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1394/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (676/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (151/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10/81 : ℝ) * a^1 * (c - b)^5 + (80/81 : ℝ) * (b - a)^6 + (80/27 : ℝ) * (b - a)^5 * (c - b)^1 + (280/81 : ℝ) * (b - a)^4 * (c - b)^2 + (160/81 : ℝ) * (b - a)^3 * (c - b)^3 + (5/9 : ℝ) * (b - a)^2 * (c - b)^4 + (5/81 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^5*b/81 + 5*a^5*c/81 + 20*a^4*b^2/81 + 4*a^4*b*c/9 + 20*a^4*c^2/81 + 10*a^3*b^3/27 + 2*a^3*b^2*c/81 + 2*a^3*b*c^2/81 + 10*a^3*c^3/27 + 20*a^2*b^4/81 + 2*a^2*b^3*c/81 - 40*a^2*b^2*c^2/9 + 2*a^2*b*c^3/81 + 20*a^2*c^4/81 + 5*a*b^5/81 + 4*a*b^4*c/9 + 2*a*b^3*c^2/81 + 2*a*b^2*c^3/81 + 4*a*b*c^4/9 + 5*a*c^5/81 + 5*b^5*c/81 + 20*b^4*c^2/81 + 10*b^3*c^3/27 + 20*b^2*c^4/81 + 5*b*c^5/81) := by
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
  have he : (-3*a^2*b^2*c^2 - 3*a^2*b^2*c - 3*a^2*b*c^2 - 3*a^2*b*c - 3*a*b^2*c^2 - 3*a*b^2*c - 3*a*b*c^2 + 6*a*b*c + 5*a*b + 5*a*c + a + 5*b*c + b + c - 3) = (5*a^5*b/81 + 5*a^5*c/81 + 20*a^4*b^2/81 + 4*a^4*b*c/9 + 20*a^4*c^2/81 + 10*a^3*b^3/27 + 2*a^3*b^2*c/81 + 2*a^3*b*c^2/81 + 10*a^3*c^3/27 + 20*a^2*b^4/81 + 2*a^2*b^3*c/81 - 40*a^2*b^2*c^2/9 + 2*a^2*b*c^3/81 + 20*a^2*c^4/81 + 5*a*b^5/81 + 4*a*b^4*c/9 + 2*a*b^3*c^2/81 + 2*a*b^2*c^3/81 + 4*a*b*c^4/9 + 5*a*c^5/81 + 5*b^5*c/81 + 20*b^4*c^2/81 + 10*b^3*c^3/27 + 20*b^2*c^4/81 + 5*b*c^5/81) := by
    linear_combination (-5*a^4*b/81 - 5*a^4*c/81 - 5*a^3*b^2/27 - 26*a^3*b*c/81 - 5*a^3*b/27 - 5*a^3*c^2/27 - 5*a^3*c/27 - 5*a^2*b^3/27 + 13*a^2*b^2*c/27 - 10*a^2*b^2/27 + 13*a^2*b*c^2/27 - 16*a^2*b*c/27 - 5*a^2*b/9 - 5*a^2*c^3/27 - 10*a^2*c^2/27 - 5*a^2*c/9 - 5*a*b^4/81 - 26*a*b^3*c/81 - 5*a*b^3/27 + 13*a*b^2*c^2/27 - 16*a*b^2*c/27 - 5*a*b^2/9 - 26*a*b*c^3/81 - 16*a*b*c^2/27 - 11*a*b*c/3 - 5*a*b/3 - 5*a*c^4/81 - 5*a*c^3/27 - 5*a*c^2/9 - 5*a*c/3 - 5*b^4*c/81 - 5*b^3*c^2/27 - 5*b^3*c/27 - 5*b^2*c^3/27 - 10*b^2*c^2/27 - 5*b^2*c/9 - 5*b*c^4/81 - 5*b*c^3/27 - 5*b*c^2/9 - 5*b*c/3 + 1) * hab
  have hn : 0 ≤ (-3*a^2*b^2*c^2 - 3*a^2*b^2*c - 3*a^2*b*c^2 - 3*a^2*b*c - 3*a*b^2*c^2 - 3*a*b^2*c - 3*a*b*c^2 + 6*a*b*c + 5*a*b + 5*a*c + a + 5*b*c + b + c - 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3), (a / (a + 1) + b / (b + 1) + c / (c + 1)) ≥ (3 * (1 + a * b * c)) / 4) := @solution
#print axioms solution
