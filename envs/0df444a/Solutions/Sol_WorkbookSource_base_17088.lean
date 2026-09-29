-- Prove2me | solution 1 for WorkbookSource.base_17088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:40.143304+00:00
-- url     : https://prove2.me/submissions/ffd32070-fd99-4f5c-8a6e-a0e185614be7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 / (b^2 + 2 * b) + b^2 / (c^2 + 2 * c) + c^2 / (a^2 + 2 * a) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^5*c/9 + 22*a^4*b*c/27 + 29*a^4*c^2/9 + 10*a^3*b^3/9 - 22*a^3*b^2*c/9 - 4*a^3*b*c^2/3 + 10*a^3*c^3/9 + 29*a^2*b^4/9 - 4*a^2*b^3*c/3 - 67*a^2*b^2*c^2/9 - 22*a^2*b*c^3/9 + 10*a*b^5/9 + 22*a*b^4*c/27 - 22*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 22*a*b*c^4/27 + 10*b^3*c^3/9 + 29*b^2*c^4/9 + 10*b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (68/3 : ℝ) * a^4 * (b - a)^2 + (68/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (68/3 : ℝ) * a^4 * (c - b)^2 + (1754/27 : ℝ) * a^3 * (b - a)^3 + (1048/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (926/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (694/27 : ℝ) * a^3 * (c - b)^3 + (1849/27 : ℝ) * a^2 * (b - a)^4 + (4724/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1649/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2072/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (259/27 : ℝ) * a^2 * (c - b)^4 + (854/27 : ℝ) * a^1 * (b - a)^5 + (2810/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1202/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (2086/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (496/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10/9 : ℝ) * a^1 * (c - b)^5 + (49/9 : ℝ) * (b - a)^6 + (196/9 : ℝ) * (b - a)^5 * (c - b)^1 + (304/9 : ℝ) * (b - a)^4 * (c - b)^2 + (226/9 : ℝ) * (b - a)^3 * (c - b)^3 + (79/9 : ℝ) * (b - a)^2 * (c - b)^4 + (10/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^5*c/9 + 22*a^4*b*c/27 + 29*a^4*c^2/9 + 10*a^3*b^3/9 - 22*a^3*b^2*c/9 - 4*a^3*b*c^2/3 + 10*a^3*c^3/9 + 29*a^2*b^4/9 - 4*a^2*b^3*c/3 - 67*a^2*b^2*c^2/9 - 22*a^2*b*c^3/9 + 10*a*b^5/9 + 22*a*b^4*c/27 - 22*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 22*a*b*c^4/27 + 10*b^3*c^3/9 + 29*b^2*c^4/9 + 10*b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (68/3 : ℝ) * a^4 * (c - a)^2 + (68/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (68/3 : ℝ) * a^4 * (b - c)^2 + (1754/27 : ℝ) * a^3 * (c - a)^3 + (706/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (584/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (694/27 : ℝ) * a^3 * (b - c)^3 + (1849/27 : ℝ) * a^2 * (c - a)^4 + (2672/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (623/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1046/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (259/27 : ℝ) * a^2 * (b - c)^4 + (854/27 : ℝ) * a^1 * (c - a)^5 + (1460/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (302/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (412/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (172/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (10/9 : ℝ) * a^1 * (b - c)^5 + (49/9 : ℝ) * (c - a)^6 + (98/9 : ℝ) * (c - a)^5 * (b - c)^1 + (59/9 : ℝ) * (c - a)^4 * (b - c)^2 + (10/9 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^5*c/9 + 22*a^4*b*c/27 + 29*a^4*c^2/9 + 10*a^3*b^3/9 - 22*a^3*b^2*c/9 - 4*a^3*b*c^2/3 + 10*a^3*c^3/9 + 29*a^2*b^4/9 - 4*a^2*b^3*c/3 - 67*a^2*b^2*c^2/9 - 22*a^2*b*c^3/9 + 10*a*b^5/9 + 22*a*b^4*c/27 - 22*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 22*a*b*c^4/27 + 10*b^3*c^3/9 + 29*b^2*c^4/9 + 10*b*c^5/9) := by
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
  have he : (a^4*c^2 + 2*a^4*c + 2*a^3*c^2 + 4*a^3*c + a^2*b^4 + 2*a^2*b^3 - a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 - 4*a^2*b*c + 2*a*b^4 + 4*a*b^3 - 2*a*b^2*c^2 - 4*a*b^2*c - 4*a*b*c^2 - 8*a*b*c + b^2*c^4 + 2*b^2*c^3 + 2*b*c^4 + 4*b*c^3) = (10*a^5*c/9 + 22*a^4*b*c/27 + 29*a^4*c^2/9 + 10*a^3*b^3/9 - 22*a^3*b^2*c/9 - 4*a^3*b*c^2/3 + 10*a^3*c^3/9 + 29*a^2*b^4/9 - 4*a^2*b^3*c/3 - 67*a^2*b^2*c^2/9 - 22*a^2*b*c^3/9 + 10*a*b^5/9 + 22*a*b^4*c/27 - 22*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 22*a*b*c^4/27 + 10*b^3*c^3/9 + 29*b^2*c^4/9 + 10*b*c^5/9) := by
    linear_combination (-10*a^4*c/9 + 8*a^3*b*c/27 - 10*a^3*c^2/9 - 4*a^3*c/3 - 10*a^2*b^3/9 + 58*a^2*b^2*c/27 + 58*a^2*b*c^2/27 + 20*a^2*b*c/9 - 10*a*b^4/9 + 8*a*b^3*c/27 - 4*a*b^3/3 + 58*a*b^2*c^2/27 + 20*a*b^2*c/9 + 8*a*b*c^3/27 + 20*a*b*c^2/9 + 8*a*b*c/3 - 10*b^2*c^3/9 - 10*b*c^4/9 - 4*b*c^3/3) * hab
  have hn : 0 ≤ (a^4*c^2 + 2*a^4*c + 2*a^3*c^2 + 4*a^3*c + a^2*b^4 + 2*a^2*b^3 - a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 - 4*a^2*b*c + 2*a*b^4 + 4*a*b^3 - 2*a*b^2*c^2 - 4*a*b^2*c - 4*a*b*c^2 - 8*a*b*c + b^2*c^4 + 2*b^2*c^3 + 2*b*c^4 + 4*b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^2 / (b^2 + 2 * b) + b^2 / (c^2 + 2 * c) + c^2 / (a^2 + 2 * a) ≥ 1) := @solution
#print axioms solution
