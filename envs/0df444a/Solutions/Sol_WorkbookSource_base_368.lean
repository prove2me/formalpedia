-- Prove2me | solution 1 for WorkbookSource.base_368
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:41.045233+00:00
-- url     : https://prove2.me/submissions/c443fd90-7caf-4eed-988a-fbdc42d556d6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / (a + 2) + b^2 / (b + 2) + c^2 / (c + 2)) ≤ 3 / (a * b + b * c + a * c)  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (20*a^6/243 + 10*a^5*b/81 + 10*a^5*c/81 - 2*a^4*b^2/81 - 25*a^4*b*c/81 - 2*a^4*c^2/81 - 32*a^3*b^3/243 - 8*a^3*b^2*c/81 - 8*a^3*b*c^2/81 - 32*a^3*c^3/243 - 2*a^2*b^4/81 - 8*a^2*b^3*c/81 + 29*a^2*b^2*c^2/27 - 8*a^2*b*c^3/81 - 2*a^2*c^4/81 + 10*a*b^5/81 - 25*a*b^4*c/81 - 8*a*b^3*c^2/81 - 8*a*b^2*c^3/81 - 25*a*b*c^4/81 + 10*a*c^5/81 + 20*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 - 32*b^3*c^3/243 - 2*b^2*c^4/81 + 10*b*c^5/81 + 20*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^4 * (b - a)^2 + (1 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^4 * (c - b)^2 + (16/9 : ℝ) * a^3 * (b - a)^3 + (8/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (16/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (20/9 : ℝ) * a^3 * (c - b)^3 + (13/9 : ℝ) * a^2 * (b - a)^4 + (26/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (68/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (19/9 : ℝ) * a^2 * (c - b)^4 + (22/27 : ℝ) * a^1 * (b - a)^5 + (55/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (178/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (212/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (107/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (20/27 : ℝ) * a^1 * (c - b)^5 + (56/243 : ℝ) * (b - a)^6 + (56/81 : ℝ) * (b - a)^5 * (c - b)^1 + (154/81 : ℝ) * (b - a)^4 * (c - b)^2 + (644/243 : ℝ) * (b - a)^3 * (c - b)^3 + (148/81 : ℝ) * (b - a)^2 * (c - b)^4 + (50/81 : ℝ) * (b - a)^1 * (c - b)^5 + (20/243 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (20*a^6/243 + 10*a^5*b/81 + 10*a^5*c/81 - 2*a^4*b^2/81 - 25*a^4*b*c/81 - 2*a^4*c^2/81 - 32*a^3*b^3/243 - 8*a^3*b^2*c/81 - 8*a^3*b*c^2/81 - 32*a^3*c^3/243 - 2*a^2*b^4/81 - 8*a^2*b^3*c/81 + 29*a^2*b^2*c^2/27 - 8*a^2*b*c^3/81 - 2*a^2*c^4/81 + 10*a*b^5/81 - 25*a*b^4*c/81 - 8*a*b^3*c^2/81 - 8*a*b^2*c^3/81 - 25*a*b*c^4/81 + 10*a*c^5/81 + 20*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 - 32*b^3*c^3/243 - 2*b^2*c^4/81 + 10*b*c^5/81 + 20*c^6/243) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^3*b^2*c - 2*a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 4*a^3*b - 2*a^3*c^2 - 4*a^3*c - a^2*b^3*c - 2*a^2*b^3 - 3*a^2*b^2*c^2 - 4*a^2*b^2*c - a^2*b*c^3 - 4*a^2*b*c^2 - 4*a^2*b*c - 2*a^2*c^3 - a*b^3*c^2 - 4*a*b^3*c - 4*a*b^3 - a*b^2*c^3 - 4*a*b^2*c^2 - 4*a*b^2*c - 4*a*b*c^3 - 4*a*b*c^2 + 3*a*b*c + 6*a*b - 4*a*c^3 + 6*a*c + 12*a - 2*b^3*c^2 - 4*b^3*c - 2*b^2*c^3 - 4*b*c^3 + 6*b*c + 12*b + 12*c + 24) = (20*a^6/243 + 10*a^5*b/81 + 10*a^5*c/81 - 2*a^4*b^2/81 - 25*a^4*b*c/81 - 2*a^4*c^2/81 - 32*a^3*b^3/243 - 8*a^3*b^2*c/81 - 8*a^3*b*c^2/81 - 32*a^3*c^3/243 - 2*a^2*b^4/81 - 8*a^2*b^3*c/81 + 29*a^2*b^2*c^2/27 - 8*a^2*b*c^3/81 - 2*a^2*c^4/81 + 10*a*b^5/81 - 25*a*b^4*c/81 - 8*a*b^3*c^2/81 - 8*a*b^2*c^3/81 - 25*a*b*c^4/81 + 10*a*c^5/81 + 20*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 - 32*b^3*c^3/243 - 2*b^2*c^4/81 + 10*b*c^5/81 + 20*c^6/243) := by
    linear_combination (-20*a^5/243 - 10*a^4*b/243 - 10*a^4*c/243 - 20*a^4/81 + 16*a^3*b^2/243 + 95*a^3*b*c/243 + 10*a^3*b/81 + 16*a^3*c^2/243 + 10*a^3*c/81 - 20*a^3/27 + 16*a^2*b^3/243 - 110*a^2*b^2*c/81 - 52*a^2*b^2/27 - 110*a^2*b*c^2/81 - 83*a^2*b*c/27 - 26*a^2*b/9 + 16*a^2*c^3/243 - 52*a^2*c^2/27 - 26*a^2*c/9 - 20*a^2/9 - 10*a*b^4/243 + 95*a*b^3*c/243 + 10*a*b^3/81 - 110*a*b^2*c^2/81 - 83*a*b^2*c/27 - 26*a*b^2/9 + 95*a*b*c^3/243 - 83*a*b*c^2/27 - 67*a*b*c/9 - 58*a*b/9 - 10*a*c^4/243 + 10*a*c^3/81 - 26*a*c^2/9 - 58*a*c/9 - 20*a/3 - 20*b^5/243 - 10*b^4*c/243 - 20*b^4/81 + 16*b^3*c^2/243 + 10*b^3*c/81 - 20*b^3/27 + 16*b^2*c^3/243 - 52*b^2*c^2/27 - 26*b^2*c/9 - 20*b^2/9 - 10*b*c^4/243 + 10*b*c^3/81 - 26*b*c^2/9 - 58*b*c/9 - 20*b/3 - 20*c^5/243 - 20*c^4/81 - 20*c^3/27 - 20*c^2/9 - 20*c/3 - 8) * hab
  have hn : 0 ≤ (-a^3*b^2*c - 2*a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 4*a^3*b - 2*a^3*c^2 - 4*a^3*c - a^2*b^3*c - 2*a^2*b^3 - 3*a^2*b^2*c^2 - 4*a^2*b^2*c - a^2*b*c^3 - 4*a^2*b*c^2 - 4*a^2*b*c - 2*a^2*c^3 - a*b^3*c^2 - 4*a*b^3*c - 4*a*b^3 - a*b^2*c^3 - 4*a*b^2*c^2 - 4*a*b^2*c - 4*a*b*c^3 - 4*a*b*c^2 + 3*a*b*c + 6*a*b - 4*a*c^3 + 6*a*c + 12*a - 2*b^3*c^2 - 4*b^3*c - 2*b^2*c^3 - 4*b*c^3 + 6*b*c + 12*b + 12*c + 24) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 / (a + 2) + b^2 / (b + 2) + c^2 / (c + 2)) ≤ 3 / (a * b + b * c + a * c)) := @solution
#print axioms solution
