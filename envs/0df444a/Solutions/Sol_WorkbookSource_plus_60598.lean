-- Prove2me | solution 1 for WorkbookSource.plus_60598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:47.475707+00:00
-- url     : https://prove2.me/submissions/ce20706a-04ca-4461-a425-85b23eddc6ff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / (1 + b^2) + b^2 / (1 + c^2) + c^2 / (1 + a^2)) ≥ 3 / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (50*a^6/243 + 10*a^5*b/27 + 10*a^5*c/27 - a^4*b^2/27 + 14*a^4*b*c/81 + 53*a^4*c^2/27 - 98*a^3*b^3/243 - 2*a^3*b^2*c/3 - 2*a^3*b*c^2/3 - 98*a^3*c^3/243 + 53*a^2*b^4/27 - 2*a^2*b^3*c/3 - 106*a^2*b^2*c^2/27 - 2*a^2*b*c^3/3 - a^2*c^4/27 + 10*a*b^5/27 + 14*a*b^4*c/81 - 2*a*b^3*c^2/3 - 2*a*b^2*c^3/3 + 14*a*b*c^4/81 + 10*a*c^5/27 + 50*b^6/243 + 10*b^5*c/27 - b^4*c^2/27 - 98*b^3*c^3/243 + 53*b^2*c^4/27 + 10*b*c^5/27 + 50*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40/3 : ℝ) * a^4 * (b - a)^2 + (40/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (40/3 : ℝ) * a^4 * (c - b)^2 + (320/9 : ℝ) * a^3 * (b - a)^3 + (184/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (184/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (160/9 : ℝ) * a^3 * (c - b)^3 + (320/9 : ℝ) * a^2 * (b - a)^4 + (784/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (104 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (472/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (80/9 : ℝ) * a^2 * (c - b)^4 + (1280/81 : ℝ) * a^1 * (b - a)^5 + (4010/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (5780/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4012/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1282/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (160/81 : ℝ) * a^1 * (c - b)^5 + (650/243 : ℝ) * (b - a)^6 + (812/81 : ℝ) * (b - a)^5 * (c - b)^1 + (1403/81 : ℝ) * (b - a)^4 * (c - b)^2 + (3710/243 : ℝ) * (b - a)^3 * (c - b)^3 + (559/81 : ℝ) * (b - a)^2 * (c - b)^4 + (130/81 : ℝ) * (b - a)^1 * (c - b)^5 + (50/243 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (50*a^6/243 + 10*a^5*b/27 + 10*a^5*c/27 - a^4*b^2/27 + 14*a^4*b*c/81 + 53*a^4*c^2/27 - 98*a^3*b^3/243 - 2*a^3*b^2*c/3 - 2*a^3*b*c^2/3 - 98*a^3*c^3/243 + 53*a^2*b^4/27 - 2*a^2*b^3*c/3 - 106*a^2*b^2*c^2/27 - 2*a^2*b*c^3/3 - a^2*c^4/27 + 10*a*b^5/27 + 14*a*b^4*c/81 - 2*a*b^3*c^2/3 - 2*a*b^2*c^3/3 + 14*a*b*c^4/81 + 10*a*c^5/27 + 50*b^6/243 + 10*b^5*c/27 - b^4*c^2/27 - 98*b^3*c^3/243 + 53*b^2*c^4/27 + 10*b*c^5/27 + 50*c^6/243) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40/3 : ℝ) * a^4 * (c - a)^2 + (40/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (40/3 : ℝ) * a^4 * (b - c)^2 + (320/9 : ℝ) * a^3 * (c - a)^3 + (136/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (136/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (160/9 : ℝ) * a^3 * (b - c)^3 + (320/9 : ℝ) * a^2 * (c - a)^4 + (496/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (56 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (328/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (80/9 : ℝ) * a^2 * (b - c)^4 + (1280/81 : ℝ) * a^1 * (c - a)^5 + (2390/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (2540/81 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (2068/81 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (958/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (160/81 : ℝ) * a^1 * (b - c)^5 + (650/243 : ℝ) * (c - a)^6 + (488/81 : ℝ) * (c - a)^5 * (b - c)^1 + (593/81 : ℝ) * (c - a)^4 * (b - c)^2 + (1766/243 : ℝ) * (c - a)^3 * (b - c)^3 + (397/81 : ℝ) * (c - a)^2 * (b - c)^4 + (130/81 : ℝ) * (c - a)^1 * (b - c)^5 + (50/243 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (50*a^6/243 + 10*a^5*b/27 + 10*a^5*c/27 - a^4*b^2/27 + 14*a^4*b*c/81 + 53*a^4*c^2/27 - 98*a^3*b^3/243 - 2*a^3*b^2*c/3 - 2*a^3*b*c^2/3 - 98*a^3*c^3/243 + 53*a^2*b^4/27 - 2*a^2*b^3*c/3 - 106*a^2*b^2*c^2/27 - 2*a^2*b*c^3/3 - a^2*c^4/27 + 10*a*b^5/27 + 14*a*b^4*c/81 - 2*a*b^3*c^2/3 - 2*a*b^2*c^3/3 + 14*a*b*c^4/81 + 10*a*c^5/27 + 50*b^6/243 + 10*b^5*c/27 - b^4*c^2/27 - 98*b^3*c^3/243 + 53*b^2*c^4/27 + 10*b*c^5/27 + 50*c^6/243) := by
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
  have he : (2*a^4*c^2 + 2*a^4 + 2*a^2*b^4 - 3*a^2*b^2*c^2 - a^2*b^2 - a^2*c^2 - a^2 + 2*b^4 + 2*b^2*c^4 - b^2*c^2 - b^2 + 2*c^4 - c^2 - 3) = (50*a^6/243 + 10*a^5*b/27 + 10*a^5*c/27 - a^4*b^2/27 + 14*a^4*b*c/81 + 53*a^4*c^2/27 - 98*a^3*b^3/243 - 2*a^3*b^2*c/3 - 2*a^3*b*c^2/3 - 98*a^3*c^3/243 + 53*a^2*b^4/27 - 2*a^2*b^3*c/3 - 106*a^2*b^2*c^2/27 - 2*a^2*b*c^3/3 - a^2*c^4/27 + 10*a*b^5/27 + 14*a*b^4*c/81 - 2*a*b^3*c^2/3 - 2*a*b^2*c^3/3 + 14*a*b*c^4/81 + 10*a*c^5/27 + 50*b^6/243 + 10*b^5*c/27 - b^4*c^2/27 - 98*b^3*c^3/243 + 53*b^2*c^4/27 + 10*b*c^5/27 + 50*c^6/243) := by
    linear_combination (-50*a^5/243 - 40*a^4*b/243 - 40*a^4*c/243 - 50*a^4/81 + 49*a^3*b^2/243 + 38*a^3*b*c/243 + 10*a^3*b/81 + 49*a^3*c^2/243 + 10*a^3*c/81 + 4*a^3/27 + 49*a^2*b^3/243 + 25*a^2*b^2*c/81 + 13*a^2*b^2/27 + 25*a^2*b*c^2/81 + 2*a^2*b*c/9 + 2*a^2*b/9 + 49*a^2*c^3/243 + 13*a^2*c^2/27 + 2*a^2*c/9 + 4*a^2/9 - 40*a*b^4/243 + 38*a*b^3*c/243 + 10*a*b^3/81 + 25*a*b^2*c^2/81 + 2*a*b^2*c/9 + 2*a*b^2/9 + 38*a*b*c^3/243 + 2*a*b*c^2/9 + 2*a*b*c/9 + 2*a*b/9 - 40*a*c^4/243 + 10*a*c^3/81 + 2*a*c^2/9 + 2*a*c/9 + a/3 - 50*b^5/243 - 40*b^4*c/243 - 50*b^4/81 + 49*b^3*c^2/243 + 10*b^3*c/81 + 4*b^3/27 + 49*b^2*c^3/243 + 13*b^2*c^2/27 + 2*b^2*c/9 + 4*b^2/9 - 40*b*c^4/243 + 10*b*c^3/81 + 2*b*c^2/9 + 2*b*c/9 + b/3 - 50*c^5/243 - 50*c^4/81 + 4*c^3/27 + 4*c^2/9 + c/3 + 1) * hab
  have hn : 0 ≤ (2*a^4*c^2 + 2*a^4 + 2*a^2*b^4 - 3*a^2*b^2*c^2 - a^2*b^2 - a^2*c^2 - a^2 + 2*b^4 + 2*b^2*c^4 - b^2*c^2 - b^2 + 2*c^4 - c^2 - 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 / (1 + b^2) + b^2 / (1 + c^2) + c^2 / (1 + a^2)) ≥ 3 / 2) := @solution
#print axioms solution
