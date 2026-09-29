-- Prove2me | solution 1 for WorkbookSource.base_13820
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:12.720793+00:00
-- url     : https://prove2.me/submissions/6e6ee865-cf5b-44fc-8bc9-ae0c0471d151

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6/27 + 13*a^5*b/81 + 13*a^5*c/81 + 106*a^4*b^2/81 - 14*a^4*b*c/9 + 106*a^4*c^2/81 + 22*a^3*b^3/9 - 335*a^3*b^2*c/81 - 335*a^3*b*c^2/81 + 22*a^3*c^3/9 + 106*a^2*b^4/81 - 335*a^2*b^3*c/81 + 118*a^2*b^2*c^2/9 - 335*a^2*b*c^3/81 + 106*a^2*c^4/81 + 13*a*b^5/81 - 14*a*b^4*c/9 - 335*a*b^3*c^2/81 - 335*a*b^2*c^3/81 - 14*a*b*c^4/9 + 13*a*c^5/81 + 2*b^6/27 + 13*b^5*c/81 + 106*b^4*c^2/81 + 22*b^3*c^3/9 + 106*b^2*c^4/81 + 13*b*c^5/81 + 2*c^6/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (238/9 : ℝ) * a^3 * (b - a)^3 + (119/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (73/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (50/9 : ℝ) * a^3 * (c - b)^3 + (316/9 : ℝ) * a^2 * (b - a)^4 + (632/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (51 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (143/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (34/9 : ℝ) * a^2 * (c - b)^4 + (1792/81 : ℝ) * a^1 * (b - a)^5 + (4480/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (4258/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1907/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (461/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (62/81 : ℝ) * a^1 * (c - b)^5 + (448/81 : ℝ) * (b - a)^6 + (448/27 : ℝ) * (b - a)^5 * (c - b)^1 + (1556/81 : ℝ) * (b - a)^4 * (c - b)^2 + (872/81 : ℝ) * (b - a)^3 * (c - b)^3 + (29/9 : ℝ) * (b - a)^2 * (c - b)^4 + (49/81 : ℝ) * (b - a)^1 * (c - b)^5 + (2/27 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6/27 + 13*a^5*b/81 + 13*a^5*c/81 + 106*a^4*b^2/81 - 14*a^4*b*c/9 + 106*a^4*c^2/81 + 22*a^3*b^3/9 - 335*a^3*b^2*c/81 - 335*a^3*b*c^2/81 + 22*a^3*c^3/9 + 106*a^2*b^4/81 - 335*a^2*b^3*c/81 + 118*a^2*b^2*c^2/9 - 335*a^2*b*c^3/81 + 106*a^2*c^4/81 + 13*a*b^5/81 - 14*a*b^4*c/9 - 335*a*b^3*c^2/81 - 335*a*b^2*c^3/81 - 14*a*b*c^4/9 + 13*a*c^5/81 + 2*b^6/27 + 13*b^5*c/81 + 106*b^4*c^2/81 + 22*b^3*c^3/9 + 106*b^2*c^4/81 + 13*b*c^5/81 + 2*c^6/27) := by
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
  have he : (24*a^2*b^2*c^2 - 4*a^2*b^2*c + 12*a^2*b^2 - 4*a^2*b*c^2 - 10*a^2*b*c - 2*a^2*b + 12*a^2*c^2 - 2*a^2*c + 6*a^2 - 4*a*b^2*c^2 - 10*a*b^2*c - 2*a*b^2 - 10*a*b*c^2 - 9*a*b*c - 5*a*b - 2*a*c^2 - 5*a*c - a + 12*b^2*c^2 - 2*b^2*c + 6*b^2 - 2*b*c^2 - 5*b*c - b + 6*c^2 - c + 3) = (2*a^6/27 + 13*a^5*b/81 + 13*a^5*c/81 + 106*a^4*b^2/81 - 14*a^4*b*c/9 + 106*a^4*c^2/81 + 22*a^3*b^3/9 - 335*a^3*b^2*c/81 - 335*a^3*b*c^2/81 + 22*a^3*c^3/9 + 106*a^2*b^4/81 - 335*a^2*b^3*c/81 + 118*a^2*b^2*c^2/9 - 335*a^2*b*c^3/81 + 106*a^2*c^4/81 + 13*a*b^5/81 - 14*a*b^4*c/9 - 335*a*b^3*c^2/81 - 335*a*b^2*c^3/81 - 14*a*b*c^4/9 + 13*a*c^5/81 + 2*b^6/27 + 13*b^5*c/81 + 106*b^4*c^2/81 + 22*b^3*c^3/9 + 106*b^2*c^4/81 + 13*b*c^5/81 + 2*c^6/27) := by
    linear_combination (-2*a^5/27 - 7*a^4*b/81 - 7*a^4*c/81 - 2*a^4/9 - 11*a^3*b^2/9 + 140*a^3*b*c/81 - a^3*b/27 - 11*a^3*c^2/9 - a^3*c/27 - 2*a^3/3 - 11*a^2*b^3/9 + 98*a^2*b^2*c/27 - 98*a^2*b^2/27 + 98*a^2*b*c^2/27 + 142*a^2*b*c/27 + 5*a^2*b/9 - 11*a^2*c^3/9 - 98*a^2*c^2/27 + 5*a^2*c/9 - 2*a^2 - 7*a*b^4/81 + 140*a*b^3*c/81 - a*b^3/27 + 98*a*b^2*c^2/27 + 142*a*b^2*c/27 + 5*a*b^2/9 + 140*a*b*c^3/81 + 142*a*b*c^2/27 + 14*a*b*c/3 + 5*a*b/3 - 7*a*c^4/81 - a*c^3/27 + 5*a*c^2/9 + 5*a*c/3 - 2*b^5/27 - 7*b^4*c/81 - 2*b^4/9 - 11*b^3*c^2/9 - b^3*c/27 - 2*b^3/3 - 11*b^2*c^3/9 - 98*b^2*c^2/27 + 5*b^2*c/9 - 2*b^2 - 7*b*c^4/81 - b*c^3/27 + 5*b*c^2/9 + 5*b*c/3 - 2*c^5/27 - 2*c^4/9 - 2*c^3/3 - 2*c^2 - 1) * habc
  have hn : 0 ≤ (24*a^2*b^2*c^2 - 4*a^2*b^2*c + 12*a^2*b^2 - 4*a^2*b*c^2 - 10*a^2*b*c - 2*a^2*b + 12*a^2*c^2 - 2*a^2*c + 6*a^2 - 4*a*b^2*c^2 - 10*a*b^2*c - 2*a*b^2 - 10*a*b*c^2 - 9*a*b*c - 5*a*b - 2*a*c^2 - 5*a*c - a + 12*b^2*c^2 - 2*b^2*c + 6*b^2 - 2*b*c^2 - 5*b*c - b + 6*c^2 - c + 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1) ≤ 3 / 4) := @solution
#print axioms solution
