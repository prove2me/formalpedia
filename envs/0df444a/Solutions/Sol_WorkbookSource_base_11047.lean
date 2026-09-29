-- Prove2me | solution 1 for WorkbookSource.base_11047
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:13.616477+00:00
-- url     : https://prove2.me/submissions/0365b3eb-830c-4609-9d65-f6d84f5327e1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b * (a + b) / (1 + a * b) + b * c * (b + c) / (1 + b * c) + c * a * (c + a) / (1 + c * a)) ≤ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7/729 + 7*a^6*b/729 + 7*a^6*c/729 + 7*a^5*b^2/243 - 4*a^5*b*c/243 + 7*a^5*c^2/243 + 35*a^4*b^3/729 + 17*a^4*b^2*c/243 + 17*a^4*b*c^2/243 + 35*a^4*c^3/729 + 35*a^3*b^4/729 + 140*a^3*b^3*c/729 - 119*a^3*b^2*c^2/243 + 140*a^3*b*c^3/729 + 35*a^3*c^4/729 + 7*a^2*b^5/243 + 17*a^2*b^4*c/243 - 119*a^2*b^3*c^2/243 - 119*a^2*b^2*c^3/243 + 17*a^2*b*c^4/243 + 7*a^2*c^5/243 + 7*a*b^6/729 - 4*a*b^5*c/243 + 17*a*b^4*c^2/243 + 140*a*b^3*c^3/729 + 17*a*b^2*c^4/243 - 4*a*b*c^5/243 + 7*a*c^6/729 + b^7/729 + 7*b^6*c/729 + 7*b^5*c^2/243 + 35*b^4*c^3/729 + 35*b^3*c^4/729 + 7*b^2*c^5/243 + 7*b*c^6/729 + c^7/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^5 * (b - a)^2 + (4/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (4/3 : ℝ) * a^5 * (c - b)^2 + (44/9 : ℝ) * a^4 * (b - a)^3 + (22/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (6 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (16/9 : ℝ) * a^4 * (c - b)^3 + (7 : ℝ) * a^3 * (b - a)^4 + (14 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (109/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (46/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (7/9 : ℝ) * a^3 * (c - b)^4 + (130/27 : ℝ) * a^2 * (b - a)^5 + (325/27 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (328/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (167/27 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (44/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (5/27 : ℝ) * a^2 * (c - b)^5 + (376/243 : ℝ) * a^1 * (b - a)^6 + (376/81 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (458/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (868/243 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (104/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (22/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (7/243 : ℝ) * a^1 * (c - b)^6 + (128/729 : ℝ) * (b - a)^7 + (448/729 : ℝ) * (b - a)^6 * (c - b)^1 + (224/243 : ℝ) * (b - a)^5 * (c - b)^2 + (560/729 : ℝ) * (b - a)^4 * (c - b)^3 + (280/729 : ℝ) * (b - a)^3 * (c - b)^4 + (28/243 : ℝ) * (b - a)^2 * (c - b)^5 + (14/729 : ℝ) * (b - a)^1 * (c - b)^6 + (1/729 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7/729 + 7*a^6*b/729 + 7*a^6*c/729 + 7*a^5*b^2/243 - 4*a^5*b*c/243 + 7*a^5*c^2/243 + 35*a^4*b^3/729 + 17*a^4*b^2*c/243 + 17*a^4*b*c^2/243 + 35*a^4*c^3/729 + 35*a^3*b^4/729 + 140*a^3*b^3*c/729 - 119*a^3*b^2*c^2/243 + 140*a^3*b*c^3/729 + 35*a^3*c^4/729 + 7*a^2*b^5/243 + 17*a^2*b^4*c/243 - 119*a^2*b^3*c^2/243 - 119*a^2*b^2*c^3/243 + 17*a^2*b*c^4/243 + 7*a^2*c^5/243 + 7*a*b^6/729 - 4*a*b^5*c/243 + 17*a*b^4*c^2/243 + 140*a*b^3*c^3/729 + 17*a*b^2*c^4/243 - 4*a*b*c^5/243 + 7*a*c^6/729 + b^7/729 + 7*b^6*c/729 + 7*b^5*c^2/243 + 35*b^4*c^3/729 + 35*b^3*c^4/729 + 7*b^2*c^5/243 + 7*b*c^6/729 + c^7/729) := by
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
  have he : (-2*a^3*b^2*c^2 - 2*a^3*b*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + 3*a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 + 3*a^2*b*c - a^2*b - a^2*c - 2*a*b^3*c - 2*a*b^2*c^2 + 3*a*b^2*c - a*b^2 - 2*a*b*c^3 + 3*a*b*c^2 + 3*a*b - a*c^2 + 3*a*c - b^2*c - b*c^2 + 3*b*c + 3) = (a^7/729 + 7*a^6*b/729 + 7*a^6*c/729 + 7*a^5*b^2/243 - 4*a^5*b*c/243 + 7*a^5*c^2/243 + 35*a^4*b^3/729 + 17*a^4*b^2*c/243 + 17*a^4*b*c^2/243 + 35*a^4*c^3/729 + 35*a^3*b^4/729 + 140*a^3*b^3*c/729 - 119*a^3*b^2*c^2/243 + 140*a^3*b*c^3/729 + 35*a^3*c^4/729 + 7*a^2*b^5/243 + 17*a^2*b^4*c/243 - 119*a^2*b^3*c^2/243 - 119*a^2*b^2*c^3/243 + 17*a^2*b*c^4/243 + 7*a^2*c^5/243 + 7*a*b^6/729 - 4*a*b^5*c/243 + 17*a*b^4*c^2/243 + 140*a*b^3*c^3/729 + 17*a*b^2*c^4/243 - 4*a*b*c^5/243 + 7*a*c^6/729 + b^7/729 + 7*b^6*c/729 + 7*b^5*c^2/243 + 35*b^4*c^3/729 + 35*b^3*c^4/729 + 7*b^2*c^5/243 + 7*b*c^6/729 + c^7/729) := by
    linear_combination (-a^6/729 - 2*a^5*b/243 - 2*a^5*c/243 - a^5/243 - 5*a^4*b^2/243 + 8*a^4*b*c/243 - 5*a^4*b/243 - 5*a^4*c^2/243 - 5*a^4*c/243 - a^4/81 - 20*a^3*b^3/729 - 20*a^3*b^2*c/243 - 10*a^3*b^2/243 - 20*a^3*b*c^2/243 + 34*a^3*b*c/243 - 4*a^3*b/81 - 20*a^3*c^3/729 - 10*a^3*c^2/243 - 4*a^3*c/81 - a^3/27 - 5*a^2*b^4/243 - 20*a^2*b^3*c/243 - 10*a^2*b^3/243 - 109*a^2*b^2*c^2/81 - 28*a^2*b^2*c/81 - 2*a^2*b^2/27 - 20*a^2*b*c^3/243 - 28*a^2*b*c^2/81 - 40*a^2*b*c/27 - a^2*b/9 - 5*a^2*c^4/243 - 10*a^2*c^3/243 - 2*a^2*c^2/27 - a^2*c/9 - a^2/9 - 2*a*b^5/243 + 8*a*b^4*c/243 - 5*a*b^4/243 - 20*a*b^3*c^2/243 + 34*a*b^3*c/243 - 4*a*b^3/81 - 20*a*b^2*c^3/243 - 28*a*b^2*c^2/81 - 40*a*b^2*c/27 - a*b^2/9 + 8*a*b*c^4/243 + 34*a*b*c^3/243 - 40*a*b*c^2/27 - 11*a*b*c/9 - 11*a*b/9 - 2*a*c^5/243 - 5*a*c^4/243 - 4*a*c^3/81 - a*c^2/9 - 11*a*c/9 - a/3 - b^6/729 - 2*b^5*c/243 - b^5/243 - 5*b^4*c^2/243 - 5*b^4*c/243 - b^4/81 - 20*b^3*c^3/729 - 10*b^3*c^2/243 - 4*b^3*c/81 - b^3/27 - 5*b^2*c^4/243 - 10*b^2*c^3/243 - 2*b^2*c^2/27 - b^2*c/9 - b^2/9 - 2*b*c^5/243 - 5*b*c^4/243 - 4*b*c^3/81 - b*c^2/9 - 11*b*c/9 - b/3 - c^6/729 - c^5/243 - c^4/81 - c^3/27 - c^2/9 - c/3 - 1) * hab
  have hn : 0 ≤ (-2*a^3*b^2*c^2 - 2*a^3*b*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + 3*a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 + 3*a^2*b*c - a^2*b - a^2*c - 2*a*b^3*c - 2*a*b^2*c^2 + 3*a*b^2*c - a*b^2 - 2*a*b*c^3 + 3*a*b*c^2 + 3*a*b - a*c^2 + 3*a*c - b^2*c - b*c^2 + 3*b*c + 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a * b * (a + b) / (1 + a * b) + b * c * (b + c) / (1 + b * c) + c * a * (c + a) / (1 + c * a)) ≤ 3) := @solution
#print axioms solution
