-- Prove2me | solution 1 for WorkbookSource.plus_11598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:09:03.50116+00:00
-- url     : https://prove2.me/submissions/d93e1c60-b00f-4adf-a4ee-917c7ab67015

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 + 1)/(a^2 + 1) + (b^3 + 1)/(b^2 + 1) + (c^3 + 1)/(c^2 + 1) ≥ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7/243 + 7*a^6*b/243 + 7*a^6*c/243 + 16*a^5*b^2/243 + 16*a^5*b*c/243 + 16*a^5*c^2/243 + a^4*b^3/9 + a^4*b^2*c/243 + a^4*b*c^2/243 + a^4*c^3/9 + a^3*b^4/9 - 16*a^3*b^3*c/243 - 104*a^3*b^2*c^2/243 - 16*a^3*b*c^3/243 + a^3*c^4/9 + 16*a^2*b^5/243 + a^2*b^4*c/243 - 104*a^2*b^3*c^2/243 - 104*a^2*b^2*c^3/243 + a^2*b*c^4/243 + 16*a^2*c^5/243 + 7*a*b^6/243 + 16*a*b^5*c/243 + a*b^4*c^2/243 - 16*a*b^3*c^3/243 + a*b^2*c^4/243 + 16*a*b*c^5/243 + 7*a*c^6/243 + 2*b^7/243 + 7*b^6*c/243 + 16*b^5*c^2/243 + b^4*c^3/9 + b^3*c^4/9 + 16*b^2*c^5/243 + 7*b*c^6/243 + 2*c^7/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^5 * (b - a)^2 + (8/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (8/3 : ℝ) * a^5 * (c - b)^2 + (28/3 : ℝ) * a^4 * (b - a)^3 + (14 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (38/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^4 * (c - b)^3 + (352/27 : ℝ) * a^3 * (b - a)^4 + (704/27 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (232/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (344/27 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (64/27 : ℝ) * a^3 * (c - b)^4 + (734/81 : ℝ) * a^2 * (b - a)^5 + (1835/81 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (2102/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (1318/81 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (433/81 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (58/81 : ℝ) * a^2 * (c - b)^5 + (760/243 : ℝ) * a^1 * (b - a)^6 + (760/81 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1018/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (2308/243 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (344/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (86/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (28/243 : ℝ) * a^1 * (c - b)^6 + (104/243 : ℝ) * (b - a)^7 + (364/243 : ℝ) * (b - a)^6 * (c - b)^1 + (566/243 : ℝ) * (b - a)^5 * (c - b)^2 + (505/243 : ℝ) * (b - a)^4 * (c - b)^3 + (94/81 : ℝ) * (b - a)^3 * (c - b)^4 + (100/243 : ℝ) * (b - a)^2 * (c - b)^5 + (7/81 : ℝ) * (b - a)^1 * (c - b)^6 + (2/243 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7/243 + 7*a^6*b/243 + 7*a^6*c/243 + 16*a^5*b^2/243 + 16*a^5*b*c/243 + 16*a^5*c^2/243 + a^4*b^3/9 + a^4*b^2*c/243 + a^4*b*c^2/243 + a^4*c^3/9 + a^3*b^4/9 - 16*a^3*b^3*c/243 - 104*a^3*b^2*c^2/243 - 16*a^3*b*c^3/243 + a^3*c^4/9 + 16*a^2*b^5/243 + a^2*b^4*c/243 - 104*a^2*b^3*c^2/243 - 104*a^2*b^2*c^3/243 + a^2*b*c^4/243 + 16*a^2*c^5/243 + 7*a*b^6/243 + 16*a*b^5*c/243 + a*b^4*c^2/243 - 16*a*b^3*c^3/243 + a*b^2*c^4/243 + 16*a*b*c^5/243 + 7*a*c^6/243 + 2*b^7/243 + 7*b^6*c/243 + 16*b^5*c^2/243 + b^4*c^3/9 + b^3*c^4/9 + 16*b^2*c^5/243 + 7*b*c^6/243 + 2*c^7/243) := by
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
  have he : (a^3*b^2*c^2 + a^3*b^2 + a^3*c^2 + a^3 + a^2*b^3*c^2 + a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*c^3 - 2*a^2*c^2 - a^2 + b^3*c^2 + b^3 + b^2*c^3 - 2*b^2*c^2 - b^2 + c^3 - c^2) = (2*a^7/243 + 7*a^6*b/243 + 7*a^6*c/243 + 16*a^5*b^2/243 + 16*a^5*b*c/243 + 16*a^5*c^2/243 + a^4*b^3/9 + a^4*b^2*c/243 + a^4*b*c^2/243 + a^4*c^3/9 + a^3*b^4/9 - 16*a^3*b^3*c/243 - 104*a^3*b^2*c^2/243 - 16*a^3*b*c^3/243 + a^3*c^4/9 + 16*a^2*b^5/243 + a^2*b^4*c/243 - 104*a^2*b^3*c^2/243 - 104*a^2*b^2*c^3/243 + a^2*b*c^4/243 + 16*a^2*c^5/243 + 7*a*b^6/243 + 16*a*b^5*c/243 + a*b^4*c^2/243 - 16*a*b^3*c^3/243 + a*b^2*c^4/243 + 16*a*b*c^5/243 + 7*a*c^6/243 + 2*b^7/243 + 7*b^6*c/243 + 16*b^5*c^2/243 + b^4*c^3/9 + b^3*c^4/9 + 16*b^2*c^5/243 + 7*b*c^6/243 + 2*c^7/243) := by
    linear_combination (-2*a^6/243 - 5*a^5*b/243 - 5*a^5*c/243 - 2*a^5/81 - 11*a^4*b^2/243 - 2*a^4*b*c/81 - a^4*b/27 - 11*a^4*c^2/243 - a^4*c/27 - 2*a^4/27 - 16*a^3*b^3/243 + 16*a^3*b^2*c/243 - 8*a^3*b^2/81 + 16*a^3*b*c^2/243 - a^3*b/27 - 16*a^3*c^3/243 - 8*a^3*c^2/81 - a^3*c/27 - 2*a^3/9 - 11*a^2*b^4/243 + 16*a^2*b^3*c/243 - 8*a^2*b^3/81 + 35*a^2*b^2*c^2/27 + 8*a^2*b^2*c/27 + 20*a^2*b^2/27 + 16*a^2*b*c^3/243 + 8*a^2*b*c^2/27 + 2*a^2*b*c/27 + a^2*b/9 - 11*a^2*c^4/243 - 8*a^2*c^3/81 + 20*a^2*c^2/27 + a^2*c/9 + a^2/3 - 5*a*b^5/243 - 2*a*b^4*c/81 - a*b^4/27 + 16*a*b^3*c^2/243 - a*b^3/27 + 16*a*b^2*c^3/243 + 8*a*b^2*c^2/27 + 2*a*b^2*c/27 + a*b^2/9 - 2*a*b*c^4/81 + 2*a*b*c^2/27 - 5*a*c^5/243 - a*c^4/27 - a*c^3/27 + a*c^2/9 - 2*b^6/243 - 5*b^5*c/243 - 2*b^5/81 - 11*b^4*c^2/243 - b^4*c/27 - 2*b^4/27 - 16*b^3*c^3/243 - 8*b^3*c^2/81 - b^3*c/27 - 2*b^3/9 - 11*b^2*c^4/243 - 8*b^2*c^3/81 + 20*b^2*c^2/27 + b^2*c/9 + b^2/3 - 5*b*c^5/243 - b*c^4/27 - b*c^3/27 + b*c^2/9 - 2*c^6/243 - 2*c^5/81 - 2*c^4/27 - 2*c^3/9 + c^2/3) * hab
  have hn : 0 ≤ (a^3*b^2*c^2 + a^3*b^2 + a^3*c^2 + a^3 + a^2*b^3*c^2 + a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*c^3 - 2*a^2*c^2 - a^2 + b^3*c^2 + b^3 + b^2*c^3 - 2*b^2*c^2 - b^2 + c^3 - c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^3 + 1)/(a^2 + 1) + (b^3 + 1)/(b^2 + 1) + (c^3 + 1)/(c^2 + 1) ≥ 3) := @solution
#print axioms solution
