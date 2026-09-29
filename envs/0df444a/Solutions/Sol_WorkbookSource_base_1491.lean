-- Prove2me | solution 1 for WorkbookSource.base_1491
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:19:19.074815+00:00
-- url     : https://prove2.me/submissions/50c3b427-8640-4c79-a8a9-025e3dcb7815

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (b^2 + 3 * a) + b / (c^2 + 3 * b) + c / (a^2 + 3 * c) ≤ (2 * a^2 + b^2) / (3 * b^2 + 9 * a) + (2 * b^2 + c^2) / (3 * c^2 + 9 * b) + (2 * c^2 + a^2) / (3 * a^2 + 9 * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + 2*a^4*b^2 - a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (72 : ℝ) * a^3 * (b - a)^3 + (107 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (83 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (24 : ℝ) * a^3 * (c - b)^3 + (81 : ℝ) * a^2 * (b - a)^4 + (160 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (132 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (53 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^2 * (c - b)^4 + (41 : ℝ) * a^1 * (b - a)^5 + (100 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (96 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (45 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^1 * (c - b)^5 + (8 : ℝ) * (b - a)^6 + (23 : ℝ) * (b - a)^5 * (c - b)^1 + (26 : ℝ) * (b - a)^4 * (c - b)^2 + (14 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b + 2*a^4*b^2 - a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (c - a)^2 + (24 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^4 * (b - c)^2 + (72 : ℝ) * a^3 * (c - a)^3 + (109 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (85 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (24 : ℝ) * a^3 * (b - c)^3 + (81 : ℝ) * a^2 * (c - a)^4 + (164 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (138 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (55 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (9 : ℝ) * a^2 * (b - c)^4 + (41 : ℝ) * a^1 * (c - a)^5 + (105 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (106 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (53 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (13 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1 : ℝ) * a^1 * (b - c)^5 + (8 : ℝ) * (c - a)^6 + (25 : ℝ) * (c - a)^5 * (b - c)^1 + (31 : ℝ) * (c - a)^4 * (b - c)^2 + (20 : ℝ) * (c - a)^3 * (b - c)^3 + (7 : ℝ) * (c - a)^2 * (b - c)^4 + (1 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + 2*a^4*b^2 - a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4) := by
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
  have he : (6*a^4*b + 2*a^4*c^2 + 6*a^3*b^2 - 9*a^3*b + 3*a^3*c^2 + 2*a^2*b^4 + 3*a^2*b^3 + 3*a^2*b^2*c^2 + 18*a^2*b*c + 6*a^2*c^3 + 18*a*b^2*c + 18*a*b*c^2 - 81*a*b*c + 6*a*c^4 - 9*a*c^3 + 6*b^4*c + 6*b^3*c^2 - 9*b^3*c + 2*b^2*c^4 + 3*b^2*c^3) = (a^5*b + 2*a^4*b^2 - a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4) := by
    linear_combination (-a^4*b - a^3*b^2 + 2*a^3*b*c + 3*a^3*b - a^3*c^2 - a^2*b^3 + 2*a^2*b^2*c + 2*a^2*b*c^2 + 3*a^2*b*c - a^2*c^3 + 2*a*b^3*c + 2*a*b^2*c^2 + 3*a*b^2*c + 2*a*b*c^3 + 3*a*b*c^2 + 27*a*b*c - a*c^4 + 3*a*c^3 - b^4*c - b^3*c^2 + 3*b^3*c - b^2*c^3) * hab
  have hn : 0 ≤ (6*a^4*b + 2*a^4*c^2 + 6*a^3*b^2 - 9*a^3*b + 3*a^3*c^2 + 2*a^2*b^4 + 3*a^2*b^3 + 3*a^2*b^2*c^2 + 18*a^2*b*c + 6*a^2*c^3 + 18*a*b^2*c + 18*a*b*c^2 - 81*a*b*c + 6*a*c^4 - 9*a*c^3 + 6*b^4*c + 6*b^3*c^2 - 9*b^3*c + 2*b^2*c^4 + 3*b^2*c^3) := by nlinarith only [hp, he]
  have hd : 0 < (3*(3*a + b^2)*(a^2 + 3*c)*(3*b + c^2)) := by positivity
  have heqrat : ( (2 * a^2 + b^2) / (3 * b^2 + 9 * a) + (2 * b^2 + c^2) / (3 * c^2 + 9 * b) + (2 * c^2 + a^2) / (3 * a^2 + 9 * c)  ) - ( a / (b^2 + 3 * a) + b / (c^2 + 3 * b) + c / (a^2 + 3 * c) ) = (6*a^4*b + 2*a^4*c^2 + 6*a^3*b^2 - 9*a^3*b + 3*a^3*c^2 + 2*a^2*b^4 + 3*a^2*b^3 + 3*a^2*b^2*c^2 + 18*a^2*b*c + 6*a^2*c^3 + 18*a*b^2*c + 18*a*b*c^2 - 81*a*b*c + 6*a*c^4 - 9*a*c^3 + 6*b^4*c + 6*b^3*c^2 - 9*b^3*c + 2*b^2*c^4 + 3*b^2*c^3) / (3*(3*a + b^2)*(a^2 + 3*c)*(3*b + c^2)) := by
    field_simp
    <;> ring
  have hzpos := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hzpos]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (b^2 + 3 * a) + b / (c^2 + 3 * b) + c / (a^2 + 3 * c) ≤ (2 * a^2 + b^2) / (3 * b^2 + 9 * a) + (2 * b^2 + c^2) / (3 * c^2 + 9 * b) + (2 * c^2 + a^2) / (3 * a^2 + 9 * c)) := @solution
#print axioms solution
