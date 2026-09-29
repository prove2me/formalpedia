-- Prove2me | solution 1 for WorkbookSource.plus_63837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:42:31.11773+00:00
-- url     : https://prove2.me/submissions/8bff185f-233f-4503-8175-7b2658ab5c9a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 - a) * (1 - a * b) / (a * (1 + c)) + (1 - b) * (1 - b * c) / (b * (1 + a)) + (1 - c) * (1 - c * a) / (c * (1 + b)) ≥ 0   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6*b/243 + a^6*c/243 + 17*a^5*b^2/243 - 22*a^5*b*c/243 + 8*a^5*c^2/243 + 28*a^4*b^3/243 + 2*a^4*b^2*c/243 - 88*a^4*b*c^2/243 + 22*a^4*c^3/243 + 22*a^3*b^4/243 + 206*a^3*b^3*c/243 - 178*a^3*b^2*c^2/243 + 206*a^3*b*c^3/243 + 28*a^3*c^4/243 + 8*a^2*b^5/243 - 88*a^2*b^4*c/243 - 178*a^2*b^3*c^2/243 - 178*a^2*b^2*c^3/243 + 2*a^2*b*c^4/243 + 17*a^2*c^5/243 + a*b^6/243 - 22*a*b^5*c/243 + 2*a*b^4*c^2/243 + 206*a*b^3*c^3/243 - 88*a*b^2*c^4/243 - 22*a*b*c^5/243 + 4*a*c^6/243 + 4*b^6*c/243 + 17*b^5*c^2/243 + 28*b^4*c^3/243 + 22*b^3*c^4/243 + 8*b^2*c^5/243 + b*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^5 * (b - a)^2 + (4/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (4/3 : ℝ) * a^5 * (c - b)^2 + (50/9 : ℝ) * a^4 * (b - a)^3 + (22/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (10/9 : ℝ) * a^4 * (c - b)^3 + (82/9 : ℝ) * a^3 * (b - a)^4 + (140/9 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (70/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (4/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (2/9 : ℝ) * a^3 * (c - b)^4 + (583/81 : ℝ) * a^2 * (b - a)^5 + (1255/81 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (826/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (146/81 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (14/81 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (11/81 : ℝ) * a^2 * (c - b)^5 + (641/243 : ℝ) * a^1 * (b - a)^6 + (566/81 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (524/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (578/243 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (31/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (10/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (5/243 : ℝ) * a^1 * (c - b)^6 + (80/243 : ℝ) * (b - a)^7 + (256/243 : ℝ) * (b - a)^6 * (c - b)^1 + (328/243 : ℝ) * (b - a)^5 * (c - b)^2 + (8/9 : ℝ) * (b - a)^4 * (c - b)^3 + (77/243 : ℝ) * (b - a)^3 * (c - b)^4 + (14/243 : ℝ) * (b - a)^2 * (c - b)^5 + (1/243 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6*b/243 + a^6*c/243 + 17*a^5*b^2/243 - 22*a^5*b*c/243 + 8*a^5*c^2/243 + 28*a^4*b^3/243 + 2*a^4*b^2*c/243 - 88*a^4*b*c^2/243 + 22*a^4*c^3/243 + 22*a^3*b^4/243 + 206*a^3*b^3*c/243 - 178*a^3*b^2*c^2/243 + 206*a^3*b*c^3/243 + 28*a^3*c^4/243 + 8*a^2*b^5/243 - 88*a^2*b^4*c/243 - 178*a^2*b^3*c^2/243 - 178*a^2*b^2*c^3/243 + 2*a^2*b*c^4/243 + 17*a^2*c^5/243 + a*b^6/243 - 22*a*b^5*c/243 + 2*a*b^4*c^2/243 + 206*a*b^3*c^3/243 - 88*a*b^2*c^4/243 - 22*a*b*c^5/243 + 4*a*c^6/243 + 4*b^6*c/243 + 17*b^5*c^2/243 + 28*b^4*c^3/243 + 22*b^3*c^4/243 + 8*b^2*c^5/243 + b*c^6/243) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^5 * (c - a)^2 + (4/3 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (4/3 : ℝ) * a^5 * (b - c)^2 + (50/9 : ℝ) * a^4 * (c - a)^3 + (28/3 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (6 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (10/9 : ℝ) * a^4 * (b - c)^3 + (82/9 : ℝ) * a^3 * (c - a)^4 + (188/9 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (142/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (2/9 : ℝ) * a^3 * (b - c)^4 + (583/81 : ℝ) * a^2 * (c - a)^5 + (1660/81 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (1636/81 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (632/81 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (95/81 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (11/81 : ℝ) * a^2 * (b - c)^5 + (641/243 : ℝ) * a^1 * (c - a)^6 + (716/81 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (899/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (1550/243 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (142/81 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (22/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (5/243 : ℝ) * a^1 * (b - c)^6 + (80/243 : ℝ) * (c - a)^7 + (304/243 : ℝ) * (c - a)^6 * (b - c)^1 + (472/243 : ℝ) * (c - a)^5 * (b - c)^2 + (128/81 : ℝ) * (c - a)^4 * (b - c)^3 + (173/243 : ℝ) * (c - a)^3 * (b - c)^4 + (41/243 : ℝ) * (c - a)^2 * (b - c)^5 + (4/243 : ℝ) * (c - a)^1 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6*b/243 + a^6*c/243 + 17*a^5*b^2/243 - 22*a^5*b*c/243 + 8*a^5*c^2/243 + 28*a^4*b^3/243 + 2*a^4*b^2*c/243 - 88*a^4*b*c^2/243 + 22*a^4*c^3/243 + 22*a^3*b^4/243 + 206*a^3*b^3*c/243 - 178*a^3*b^2*c^2/243 + 206*a^3*b*c^3/243 + 28*a^3*c^4/243 + 8*a^2*b^5/243 - 88*a^2*b^4*c/243 - 178*a^2*b^3*c^2/243 - 178*a^2*b^2*c^3/243 + 2*a^2*b*c^4/243 + 17*a^2*c^5/243 + a*b^6/243 - 22*a*b^5*c/243 + 2*a*b^4*c^2/243 + 206*a*b^3*c^3/243 - 88*a*b^2*c^4/243 - 22*a*b*c^5/243 + 4*a*c^6/243 + 4*b^6*c/243 + 17*b^5*c^2/243 + 28*b^4*c^3/243 + 22*b^3*c^4/243 + 8*b^2*c^5/243 + b*c^6/243) := by
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
  have he : (a^3*b^3*c + a^3*b^2*c + a^3*b*c^3 - a^3*b*c - a^2*b^2*c + a^2*b*c^3 - a^2*b*c^2 - 2*a^2*b*c + a^2*b + a*b^3*c^3 + a*b^3*c^2 - a*b^3*c - a*b^2*c^2 - 2*a*b^2*c - a*b*c^3 - 2*a*b*c^2 + a*b + a*c^2 + a*c + b^2*c + b*c) = (4*a^6*b/243 + a^6*c/243 + 17*a^5*b^2/243 - 22*a^5*b*c/243 + 8*a^5*c^2/243 + 28*a^4*b^3/243 + 2*a^4*b^2*c/243 - 88*a^4*b*c^2/243 + 22*a^4*c^3/243 + 22*a^3*b^4/243 + 206*a^3*b^3*c/243 - 178*a^3*b^2*c^2/243 + 206*a^3*b*c^3/243 + 28*a^3*c^4/243 + 8*a^2*b^5/243 - 88*a^2*b^4*c/243 - 178*a^2*b^3*c^2/243 - 178*a^2*b^2*c^3/243 + 2*a^2*b*c^4/243 + 17*a^2*c^5/243 + a*b^6/243 - 22*a*b^5*c/243 + 2*a*b^4*c^2/243 + 206*a*b^3*c^3/243 - 88*a*b^2*c^4/243 - 22*a*b*c^5/243 + 4*a*c^6/243 + 4*b^6*c/243 + 17*b^5*c^2/243 + 28*b^4*c^3/243 + 22*b^3*c^4/243 + 8*b^2*c^5/243 + b*c^6/243) := by
    linear_combination (-4*a^5*b/243 - a^5*c/243 - 13*a^4*b^2/243 + a^4*b*c/9 - 4*a^4*b/81 - 7*a^4*c^2/243 - a^4*c/81 - 5*a^3*b^3/81 - 16*a^3*b^2*c/243 - a^3*b^2/9 + 68*a^3*b*c^2/243 + 32*a^3*b*c/81 - 4*a^3*b/27 - 5*a^3*c^3/81 - 2*a^3*c^2/27 - a^3*c/27 - 7*a^2*b^4/243 + 68*a^2*b^3*c/243 - 2*a^2*b^3/27 + 14*a^2*b^2*c^2/27 + 14*a^2*b^2*c/27 - 5*a^2*b^2/27 - 16*a^2*b*c^3/243 + 14*a^2*b*c^2/27 + 10*a^2*b*c/27 - 4*a^2*b/9 - 13*a^2*c^4/243 - a^2*c^3/9 - 5*a^2*c^2/27 - a^2*c/9 - a*b^5/243 + a*b^4*c/9 - a*b^4/81 - 16*a*b^3*c^2/243 + 32*a*b^3*c/81 - a*b^3/27 + 68*a*b^2*c^3/243 + 14*a*b^2*c^2/27 + 10*a*b^2*c/27 - a*b^2/9 + a*b*c^4/9 + 32*a*b*c^3/81 + 10*a*b*c^2/27 - a*b*c/3 - a*b/3 - 4*a*c^5/243 - 4*a*c^4/81 - 4*a*c^3/27 - 4*a*c^2/9 - a*c/3 - 4*b^5*c/243 - 13*b^4*c^2/243 - 4*b^4*c/81 - 5*b^3*c^3/81 - b^3*c^2/9 - 4*b^3*c/27 - 7*b^2*c^4/243 - 2*b^2*c^3/27 - 5*b^2*c^2/27 - 4*b^2*c/9 - b*c^5/243 - b*c^4/81 - b*c^3/27 - b*c^2/9 - b*c/3) * hab
  have hn : 0 ≤ (a^3*b^3*c + a^3*b^2*c + a^3*b*c^3 - a^3*b*c - a^2*b^2*c + a^2*b*c^3 - a^2*b*c^2 - 2*a^2*b*c + a^2*b + a*b^3*c^3 + a*b^3*c^2 - a*b^3*c - a*b^2*c^2 - 2*a*b^2*c - a*b*c^3 - 2*a*b*c^2 + a*b + a*c^2 + a*c + b^2*c + b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (1 - a) * (1 - a * b) / (a * (1 + c)) + (1 - b) * (1 - b * c) / (b * (1 + a)) + (1 - c) * (1 - c * a) / (c * (1 + b)) ≥ 0) := @solution
#print axioms solution
