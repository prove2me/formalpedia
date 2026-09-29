-- Prove2me | solution 1 for WorkbookSource.base_53071
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:03:58.504109+00:00
-- url     : https://prove2.me/submissions/7d4c7f91-f2e8-45af-adba-c1eef1a631a0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (2 * b + 1) + b / (2 * c + 1) + c / (2 * a + 1) ≤ 1 / (a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^6/729 + 26*a^5*b/243 + 26*a^5*c/243 + 83*a^4*b^2/243 + 61*a^4*b*c/243 + 83*a^4*c^2/243 + 356*a^3*b^3/729 + 215*a^3*b^2*c/243 - 757*a^3*b*c^2/243 + 356*a^3*c^3/729 + 83*a^2*b^4/243 - 757*a^2*b^3*c/243 + 142*a^2*b^2*c^2/81 + 215*a^2*b*c^3/243 + 83*a^2*c^4/243 + 26*a*b^5/243 + 61*a*b^4*c/243 + 215*a*b^3*c^2/243 - 757*a*b^2*c^3/243 + 61*a*b*c^4/243 + 26*a*c^5/243 + 7*b^6/729 + 26*b^5*c/243 + 83*b^4*c^2/243 + 356*b^3*c^3/729 + 83*b^2*c^4/243 + 26*b*c^5/243 + 7*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13/3 : ℝ) * a^4 * (b - a)^2 + (13/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (13/3 : ℝ) * a^4 * (c - b)^2 + (338/27 : ℝ) * a^3 * (b - a)^3 + (151/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (125/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (130/27 : ℝ) * a^3 * (c - b)^3 + (370/27 : ℝ) * a^2 * (b - a)^4 + (632/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (173/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (257/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (58/27 : ℝ) * a^2 * (c - b)^4 + (560/81 : ℝ) * a^1 * (b - a)^5 + (1238/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1166/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (673/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (229/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (22/81 : ℝ) * a^1 * (c - b)^5 + (1024/729 : ℝ) * (b - a)^6 + (1024/243 : ℝ) * (b - a)^5 * (c - b)^1 + (1232/243 : ℝ) * (b - a)^4 * (c - b)^2 + (2272/729 : ℝ) * (b - a)^3 * (c - b)^3 + (248/243 : ℝ) * (b - a)^2 * (c - b)^4 + (40/243 : ℝ) * (b - a)^1 * (c - b)^5 + (7/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (7*a^6/729 + 26*a^5*b/243 + 26*a^5*c/243 + 83*a^4*b^2/243 + 61*a^4*b*c/243 + 83*a^4*c^2/243 + 356*a^3*b^3/729 + 215*a^3*b^2*c/243 - 757*a^3*b*c^2/243 + 356*a^3*c^3/729 + 83*a^2*b^4/243 - 757*a^2*b^3*c/243 + 142*a^2*b^2*c^2/81 + 215*a^2*b*c^3/243 + 83*a^2*c^4/243 + 26*a*b^5/243 + 61*a*b^4*c/243 + 215*a*b^3*c^2/243 - 757*a*b^2*c^3/243 + 61*a*b*c^4/243 + 26*a*c^5/243 + 7*b^6/729 + 26*b^5*c/243 + 83*b^4*c^2/243 + 356*b^3*c^3/729 + 83*b^2*c^4/243 + 26*b*c^5/243 + 7*c^6/729) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (13/3 : ℝ) * a^4 * (c - a)^2 + (13/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (13/3 : ℝ) * a^4 * (b - c)^2 + (338/27 : ℝ) * a^3 * (c - a)^3 + (187/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (161/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (130/27 : ℝ) * a^3 * (b - c)^3 + (370/27 : ℝ) * a^2 * (c - a)^4 + (848/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (281/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (365/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (58/27 : ℝ) * a^2 * (b - c)^4 + (560/81 : ℝ) * a^1 * (c - a)^5 + (1562/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1814/81 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (997/81 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (229/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (22/81 : ℝ) * a^1 * (b - c)^5 + (1024/729 : ℝ) * (c - a)^6 + (1024/243 : ℝ) * (c - a)^5 * (b - c)^1 + (1232/243 : ℝ) * (c - a)^4 * (b - c)^2 + (2272/729 : ℝ) * (c - a)^3 * (b - c)^3 + (248/243 : ℝ) * (c - a)^2 * (b - c)^4 + (40/243 : ℝ) * (c - a)^1 * (b - c)^5 + (7/729 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^6/729 + 26*a^5*b/243 + 26*a^5*c/243 + 83*a^4*b^2/243 + 61*a^4*b*c/243 + 83*a^4*c^2/243 + 356*a^3*b^3/729 + 215*a^3*b^2*c/243 - 757*a^3*b*c^2/243 + 356*a^3*c^3/729 + 83*a^2*b^4/243 - 757*a^2*b^3*c/243 + 142*a^2*b^2*c^2/81 + 215*a^2*b*c^3/243 + 83*a^2*c^4/243 + 26*a*b^5/243 + 61*a*b^4*c/243 + 215*a*b^3*c^2/243 - 757*a*b^2*c^3/243 + 61*a*b*c^4/243 + 26*a*c^5/243 + 7*b^6/729 + 26*b^5*c/243 + 83*b^4*c^2/243 + 356*b^3*c^3/729 + 83*b^2*c^4/243 + 26*b*c^5/243 + 7*c^6/729) := by
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
  have he : (-4*a^3*b*c^2 - 2*a^3*b*c - 4*a^2*b^3*c - 2*a^2*b^2*c - 2*a^2*b*c^2 - a^2*b*c - 2*a*b^3*c - 4*a*b^2*c^3 - 2*a*b^2*c^2 - a*b^2*c - 2*a*b*c^3 - a*b*c^2 + 8*a*b*c + 4*a*b + 4*a*c + 2*a + 4*b*c + 2*b + 2*c + 1) = (7*a^6/729 + 26*a^5*b/243 + 26*a^5*c/243 + 83*a^4*b^2/243 + 61*a^4*b*c/243 + 83*a^4*c^2/243 + 356*a^3*b^3/729 + 215*a^3*b^2*c/243 - 757*a^3*b*c^2/243 + 356*a^3*c^3/729 + 83*a^2*b^4/243 - 757*a^2*b^3*c/243 + 142*a^2*b^2*c^2/81 + 215*a^2*b*c^3/243 + 83*a^2*c^4/243 + 26*a*b^5/243 + 61*a*b^4*c/243 + 215*a*b^3*c^2/243 - 757*a*b^2*c^3/243 + 61*a*b*c^4/243 + 26*a*c^5/243 + 7*b^6/729 + 26*b^5*c/243 + 83*b^4*c^2/243 + 356*b^3*c^3/729 + 83*b^2*c^4/243 + 26*b*c^5/243 + 7*c^6/729) := by
    linear_combination (-7*a^5/729 - 71*a^4*b/729 - 71*a^4*c/729 - 7*a^4/243 - 178*a^3*b^2/729 - 41*a^3*b*c/729 - 64*a^3*b/243 - 178*a^3*c^2/729 - 64*a^3*c/243 - 7*a^3/81 - 178*a^2*b^3/729 - 142*a^2*b^2*c/243 - 38*a^2*b^2/81 - 142*a^2*b*c^2/243 - 133*a^2*b*c/81 - 19*a^2*b/27 - 178*a^2*c^3/729 - 38*a^2*c^2/81 - 19*a^2*c/27 - 7*a^2/27 - 71*a*b^4/729 - 41*a*b^3*c/729 - 64*a*b^3/243 - 142*a*b^2*c^2/243 - 133*a*b^2*c/81 - 19*a*b^2/27 - 41*a*b*c^3/729 - 133*a*b*c^2/81 - 122*a*b*c/27 - 50*a*b/27 - 71*a*c^4/729 - 64*a*c^3/243 - 19*a*c^2/27 - 50*a*c/27 - 7*a/9 - 7*b^5/729 - 71*b^4*c/729 - 7*b^4/243 - 178*b^3*c^2/729 - 64*b^3*c/243 - 7*b^3/81 - 178*b^2*c^3/729 - 38*b^2*c^2/81 - 19*b^2*c/27 - 7*b^2/27 - 71*b*c^4/729 - 64*b*c^3/243 - 19*b*c^2/27 - 50*b*c/27 - 7*b/9 - 7*c^5/729 - 7*c^4/243 - 7*c^3/81 - 7*c^2/27 - 7*c/9 - 1/3) * hab
  have hn : 0 ≤ (-4*a^3*b*c^2 - 2*a^3*b*c - 4*a^2*b^3*c - 2*a^2*b^2*c - 2*a^2*b*c^2 - a^2*b*c - 2*a*b^3*c - 4*a*b^2*c^3 - 2*a*b^2*c^2 - a*b^2*c - 2*a*b*c^3 - a*b*c^2 + 8*a*b*c + 4*a*b + 4*a*c + 2*a + 4*b*c + 2*b + 2*c + 1) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (2 * b + 1) + b / (2 * c + 1) + c / (2 * a + 1) ≤ 1 / (a * b * c)) := @solution
#print axioms solution
