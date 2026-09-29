-- Prove2me | solution 1 for WorkbookSource.plus_38244
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:58:33.791723+00:00
-- url     : https://prove2.me/submissions/7eb80433-0601-44b3-a68c-5fd92a51b477

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (2 * a * (a + 1) + c * a + b) + 1 / (2 * b * (b + 1) + a * b + c) + 1 / (2 * c * (c + 1) + b * c + a) ≥ 1 / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6/81 + 8*a^5*b/27 + 28*a^5*c/27 + 25*a^4*b^2/27 + 40*a^4*b*c/27 + 83*a^4*c^2/27 + 248*a^3*b^3/81 - 64*a^3*b^2*c/27 - 80*a^3*b*c^2/27 + 248*a^3*c^3/81 + 83*a^2*b^4/27 - 80*a^2*b^3*c/27 - 128*a^2*b^2*c^2/9 - 64*a^2*b*c^3/27 + 25*a^2*c^4/27 + 28*a*b^5/27 + 40*a*b^4*c/27 - 64*a*b^3*c^2/27 - 80*a*b^2*c^3/27 + 40*a*b*c^4/27 + 8*a*c^5/27 + 16*b^6/81 + 8*b^5*c/27 + 25*b^4*c^2/27 + 248*b^3*c^3/81 + 83*b^2*c^4/27 + 28*b*c^5/27 + 16*c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (b - a)^2 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^4 * (c - b)^2 + (104 : ℝ) * a^3 * (b - a)^3 + (168 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (144 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (40 : ℝ) * a^3 * (c - b)^3 + (1000/9 : ℝ) * a^2 * (b - a)^4 + (2216/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (712/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (920/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (136/9 : ℝ) * a^2 * (c - b)^4 + (1396/27 : ℝ) * a^1 * (b - a)^5 + (3922/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (4540/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (2564/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (686/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (68/27 : ℝ) * a^1 * (c - b)^5 + (712/81 : ℝ) * (b - a)^6 + (30 : ℝ) * (b - a)^5 * (c - b)^1 + (377/9 : ℝ) * (b - a)^4 * (c - b)^2 + (2404/81 : ℝ) * (b - a)^3 * (c - b)^3 + (101/9 : ℝ) * (b - a)^2 * (c - b)^4 + (20/9 : ℝ) * (b - a)^1 * (c - b)^5 + (16/81 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (16*a^6/81 + 8*a^5*b/27 + 28*a^5*c/27 + 25*a^4*b^2/27 + 40*a^4*b*c/27 + 83*a^4*c^2/27 + 248*a^3*b^3/81 - 64*a^3*b^2*c/27 - 80*a^3*b*c^2/27 + 248*a^3*c^3/81 + 83*a^2*b^4/27 - 80*a^2*b^3*c/27 - 128*a^2*b^2*c^2/9 - 64*a^2*b*c^3/27 + 25*a^2*c^4/27 + 28*a*b^5/27 + 40*a*b^4*c/27 - 64*a*b^3*c^2/27 - 80*a*b^2*c^3/27 + 40*a*b*c^4/27 + 8*a*c^5/27 + 16*b^6/81 + 8*b^5*c/27 + 25*b^4*c^2/27 + 248*b^3*c^3/81 + 83*b^2*c^4/27 + 28*b*c^5/27 + 16*c^6/81) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (c - a)^2 + (36 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (36 : ℝ) * a^4 * (b - c)^2 + (104 : ℝ) * a^3 * (c - a)^3 + (144 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (120 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (40 : ℝ) * a^3 * (b - c)^3 + (1000/9 : ℝ) * a^2 * (c - a)^4 + (1784/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (496/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (704/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (136/9 : ℝ) * a^2 * (b - c)^4 + (1396/27 : ℝ) * a^1 * (c - a)^5 + (3058/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (2812/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1484/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (470/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (68/27 : ℝ) * a^1 * (b - c)^5 + (712/81 : ℝ) * (c - a)^6 + (614/27 : ℝ) * (c - a)^5 * (b - c)^1 + (641/27 : ℝ) * (c - a)^4 * (b - c)^2 + (1108/81 : ℝ) * (c - a)^3 * (b - c)^3 + (145/27 : ℝ) * (c - a)^2 * (b - c)^4 + (40/27 : ℝ) * (c - a)^1 * (b - c)^5 + (16/81 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6/81 + 8*a^5*b/27 + 28*a^5*c/27 + 25*a^4*b^2/27 + 40*a^4*b*c/27 + 83*a^4*c^2/27 + 248*a^3*b^3/81 - 64*a^3*b^2*c/27 - 80*a^3*b*c^2/27 + 248*a^3*c^3/81 + 83*a^2*b^4/27 - 80*a^2*b^3*c/27 - 128*a^2*b^2*c^2/9 - 64*a^2*b*c^3/27 + 25*a^2*c^4/27 + 28*a*b^5/27 + 40*a*b^4*c/27 - 64*a*b^3*c^2/27 - 80*a*b^2*c^3/27 + 40*a*b*c^4/27 + 8*a*c^5/27 + 16*b^6/81 + 8*b^5*c/27 + 25*b^4*c^2/27 + 248*b^3*c^3/81 + 83*b^2*c^4/27 + 28*b*c^5/27 + 16*c^6/81) := by
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
  have he : (-2*a^4*b - 2*a^3*b^2*c - 4*a^3*b^2 - 4*a^3*b*c^2 - 5*a^3*b*c - 2*a^3*b - 2*a^3*c + 4*a^3 - 4*a^2*b^3*c - 9*a^2*b^2*c^2 - 16*a^2*b^2*c + 3*a^2*b^2 - 2*a^2*b*c^3 - 16*a^2*b*c^2 - 8*a^2*b*c + 10*a^2*b - 4*a^2*c^3 + 3*a^2*c^2 + 12*a^2*c + 4*a^2 - 2*a*b^3*c^2 - 5*a*b^3*c - 2*a*b^3 - 4*a*b^2*c^3 - 16*a*b^2*c^2 - 8*a*b^2*c + 12*a*b^2 - 5*a*b*c^3 - 8*a*b*c^2 + 3*a*b*c + 14*a*b - 2*a*c^4 - 2*a*c^3 + 10*a*c^2 + 14*a*c - 2*b^4*c - 4*b^3*c^2 - 2*b^3*c + 4*b^3 + 3*b^2*c^2 + 10*b^2*c + 4*b^2 - 2*b*c^3 + 12*b*c^2 + 14*b*c + 4*c^3 + 4*c^2) = (16*a^6/81 + 8*a^5*b/27 + 28*a^5*c/27 + 25*a^4*b^2/27 + 40*a^4*b*c/27 + 83*a^4*c^2/27 + 248*a^3*b^3/81 - 64*a^3*b^2*c/27 - 80*a^3*b*c^2/27 + 248*a^3*c^3/81 + 83*a^2*b^4/27 - 80*a^2*b^3*c/27 - 128*a^2*b^2*c^2/9 - 64*a^2*b*c^3/27 + 25*a^2*c^4/27 + 28*a*b^5/27 + 40*a*b^4*c/27 - 64*a*b^3*c^2/27 - 80*a*b^2*c^3/27 + 40*a*b*c^4/27 + 8*a*c^5/27 + 16*b^6/81 + 8*b^5*c/27 + 25*b^4*c^2/27 + 248*b^3*c^3/81 + 83*b^2*c^4/27 + 28*b*c^5/27 + 16*c^6/81) := by
    linear_combination (-16*a^5/81 - 8*a^4*b/81 - 68*a^4*c/81 - 16*a^4/27 - 67*a^3*b^2/81 - 44*a^3*b*c/81 - 46*a^3*b/27 - 181*a^3*c^2/81 - 52*a^3*c/27 - 16*a^3/9 - 181*a^2*b^3/81 + 47*a^2*b^2*c/27 - 43*a^2*b^2/9 + 47*a^2*b*c^2/27 - 3*a^2*b*c - 16*a^2*b/3 - 67*a^2*c^3/81 - 43*a^2*c^2/9 - 6*a^2*c - 4*a^2/3 - 68*a*b^4/81 - 44*a*b^3*c/81 - 52*a*b^3/27 + 47*a*b^2*c^2/27 - 3*a*b^2*c - 6*a*b^2 - 44*a*b*c^3/81 - 3*a*b*c^2 - 17*a*b*c/3 - 14*a*b/3 - 8*a*c^4/81 - 46*a*c^3/27 - 16*a*c^2/3 - 14*a*c/3 - 16*b^5/81 - 8*b^4*c/81 - 16*b^4/27 - 67*b^3*c^2/81 - 46*b^3*c/27 - 16*b^3/9 - 181*b^2*c^3/81 - 43*b^2*c^2/9 - 16*b^2*c/3 - 4*b^2/3 - 68*b*c^4/81 - 52*b*c^3/27 - 6*b*c^2 - 14*b*c/3 - 16*c^5/81 - 16*c^4/27 - 16*c^3/9 - 4*c^2/3) * hab
  have hn : 0 ≤ (-2*a^4*b - 2*a^3*b^2*c - 4*a^3*b^2 - 4*a^3*b*c^2 - 5*a^3*b*c - 2*a^3*b - 2*a^3*c + 4*a^3 - 4*a^2*b^3*c - 9*a^2*b^2*c^2 - 16*a^2*b^2*c + 3*a^2*b^2 - 2*a^2*b*c^3 - 16*a^2*b*c^2 - 8*a^2*b*c + 10*a^2*b - 4*a^2*c^3 + 3*a^2*c^2 + 12*a^2*c + 4*a^2 - 2*a*b^3*c^2 - 5*a*b^3*c - 2*a*b^3 - 4*a*b^2*c^3 - 16*a*b^2*c^2 - 8*a*b^2*c + 12*a*b^2 - 5*a*b*c^3 - 8*a*b*c^2 + 3*a*b*c + 14*a*b - 2*a*c^4 - 2*a*c^3 + 10*a*c^2 + 14*a*c - 2*b^4*c - 4*b^3*c^2 - 2*b^3*c + 4*b^3 + 3*b^2*c^2 + 10*b^2*c + 4*b^2 - 2*b*c^3 + 12*b*c^2 + 14*b*c + 4*c^3 + 4*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 1 / (2 * a * (a + 1) + c * a + b) + 1 / (2 * b * (b + 1) + a * b + c) + 1 / (2 * c * (c + 1) + b * c + a) ≥ 1 / 2) := @solution
#print axioms solution
