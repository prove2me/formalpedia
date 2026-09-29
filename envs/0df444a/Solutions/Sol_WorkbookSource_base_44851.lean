-- Prove2me | solution 1 for WorkbookSource.base_44851
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:57:01.546409+00:00
-- url     : https://prove2.me/submissions/f0831405-f254-4d84-94f1-fa3a5defc0b1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6) : a / (b * b + c) + b / (c * c + a) + c / (a * a + b) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/36 + 13*a^5*b/216 + a^5*c/36 - a^4*b^2/8 + a^4*b*c/27 + 31*a^4*c^2/216 - a^3*b^3/72 - 5*a^3*b^2*c/54 + 5*a^3*b*c^2/24 - a^3*c^3/72 + 31*a^2*b^4/216 + 5*a^2*b^3*c/24 - 59*a^2*b^2*c^2/72 - 5*a^2*b*c^3/54 - a^2*c^4/8 + a*b^5/36 + a*b^4*c/27 - 5*a*b^3*c^2/54 + 5*a*b^2*c^3/24 + a*b*c^4/27 + 13*a*c^5/216 + b^6/36 + 13*b^5*c/216 - b^4*c^2/8 - b^3*c^3/72 + 31*b^2*c^4/216 + b*c^5/36 + c^6/36) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (29/24 : ℝ) * a^4 * (b - a)^2 + (29/24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (29/24 : ℝ) * a^4 * (c - b)^2 + (667/216 : ℝ) * a^3 * (b - a)^3 + (205/36 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (439/72 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (377/216 : ℝ) * a^3 * (c - b)^3 + (79/27 : ℝ) * a^2 * (b - a)^4 + (1723/216 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (95/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1189/216 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (197/216 : ℝ) * a^2 * (c - b)^4 + (7/6 : ℝ) * a^1 * (b - a)^5 + (25/6 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1493/216 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (185/36 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (125/72 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (55/216 : ℝ) * a^1 * (c - b)^5 + (4/27 : ℝ) * (b - a)^6 + (35/54 : ℝ) * (b - a)^5 * (c - b)^1 + (25/18 : ℝ) * (b - a)^4 * (c - b)^2 + (301/216 : ℝ) * (b - a)^3 * (c - b)^3 + (151/216 : ℝ) * (b - a)^2 * (c - b)^4 + (7/36 : ℝ) * (b - a)^1 * (c - b)^5 + (1/36 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6/36 + 13*a^5*b/216 + a^5*c/36 - a^4*b^2/8 + a^4*b*c/27 + 31*a^4*c^2/216 - a^3*b^3/72 - 5*a^3*b^2*c/54 + 5*a^3*b*c^2/24 - a^3*c^3/72 + 31*a^2*b^4/216 + 5*a^2*b^3*c/24 - 59*a^2*b^2*c^2/72 - 5*a^2*b*c^3/54 - a^2*c^4/8 + a*b^5/36 + a*b^4*c/27 - 5*a*b^3*c^2/54 + 5*a*b^2*c^3/24 + a*b*c^4/27 + 13*a*c^5/216 + b^6/36 + 13*b^5*c/216 - b^4*c^2/8 - b^3*c^3/72 + 31*b^2*c^4/216 + b*c^5/36 + c^6/36) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (29/24 : ℝ) * a^4 * (c - a)^2 + (29/24 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (29/24 : ℝ) * a^4 * (b - c)^2 + (667/216 : ℝ) * a^3 * (c - a)^3 + (257/72 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (143/36 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (377/216 : ℝ) * a^3 * (b - c)^3 + (79/27 : ℝ) * a^2 * (c - a)^4 + (805/216 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (301/72 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (365/108 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (197/216 : ℝ) * a^2 * (b - c)^4 + (7/6 : ℝ) * a^1 * (c - a)^5 + (5/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (413/216 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (163/72 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (49/36 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (55/216 : ℝ) * a^1 * (b - c)^5 + (4/27 : ℝ) * (c - a)^6 + (13/54 : ℝ) * (c - a)^5 * (b - c)^1 + (10/27 : ℝ) * (c - a)^4 * (b - c)^2 + (139/216 : ℝ) * (c - a)^3 * (b - c)^3 + (16/27 : ℝ) * (c - a)^2 * (b - c)^4 + (49/216 : ℝ) * (c - a)^1 * (b - c)^5 + (1/36 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/36 + 13*a^5*b/216 + a^5*c/36 - a^4*b^2/8 + a^4*b*c/27 + 31*a^4*c^2/216 - a^3*b^3/72 - 5*a^3*b^2*c/54 + 5*a^3*b*c^2/24 - a^3*c^3/72 + 31*a^2*b^4/216 + 5*a^2*b^3*c/24 - 59*a^2*b^2*c^2/72 - 5*a^2*b*c^3/54 - a^2*c^4/8 + a*b^5/36 + a*b^4*c/27 - 5*a*b^3*c^2/54 + 5*a*b^2*c^3/24 + a*b*c^4/27 + 13*a*c^5/216 + b^6/36 + 13*b^5*c/216 - b^4*c^2/8 - b^3*c^3/72 + 31*b^2*c^4/216 + b*c^5/36 + c^6/36) := by
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
  have he : (a^4 - a^3*b^2 + a^3*c^2 - a^3*c + a^2*b^3 - a^2*b^2*c^2 + a^2*b*c + a^2*b - a^2*c^3 - a*b^3 + a*b^2*c + a*b*c^2 - a*b*c + a*c^2 + b^4 - b^3*c^2 + b^2*c^3 + b^2*c - b*c^3 + c^4) = (a^6/36 + 13*a^5*b/216 + a^5*c/36 - a^4*b^2/8 + a^4*b*c/27 + 31*a^4*c^2/216 - a^3*b^3/72 - 5*a^3*b^2*c/54 + 5*a^3*b*c^2/24 - a^3*c^3/72 + 31*a^2*b^4/216 + 5*a^2*b^3*c/24 - 59*a^2*b^2*c^2/72 - 5*a^2*b*c^3/54 - a^2*c^4/8 + a*b^5/36 + a*b^4*c/27 - 5*a*b^3*c^2/54 + 5*a*b^2*c^3/24 + a*b*c^4/27 + 13*a*c^5/216 + b^6/36 + 13*b^5*c/216 - b^4*c^2/8 - b^3*c^3/72 + 31*b^2*c^4/216 + b*c^5/36 + c^6/36) := by
    linear_combination (-a^5/36 - 7*a^4*b/216 - a^4/6 + 17*a^3*b^2/108 - a^3*b*c/216 - a^3*b/36 - 31*a^3*c^2/216 + a^3*c/6 - 31*a^2*b^3/216 - 13*a^2*b^2*c/216 - a^2*b^2/36 - 13*a^2*b*c^2/216 - a^2*b*c/6 - a^2*b/6 + 17*a^2*c^3/108 - a^2*c^2/36 - a*b^3*c/216 + a*b^3/6 - 13*a*b^2*c^2/216 - a*b^2*c/6 - a*b*c^3/216 - a*b*c^2/6 + a*b*c/6 - 7*a*c^4/216 - a*c^3/36 - a*c^2/6 - b^5/36 - 7*b^4*c/216 - b^4/6 + 17*b^3*c^2/108 - b^3*c/36 - 31*b^2*c^3/216 - b^2*c^2/36 - b^2*c/6 + b*c^3/6 - c^5/36 - c^4/6) * habc
  have hn : 0 ≤ (a^4 - a^3*b^2 + a^3*c^2 - a^3*c + a^2*b^3 - a^2*b^2*c^2 + a^2*b*c + a^2*b - a^2*c^3 - a*b^3 + a*b^2*c + a*b*c^2 - a*b*c + a*c^2 + b^4 - b^3*c^2 + b^2*c^3 + b^2*c - b*c^3 + c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6), a / (b * b + c) + b / (c * c + a) + c / (a * a + b) ≥ 1) := @solution
#print axioms solution
