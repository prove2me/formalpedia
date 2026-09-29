-- Prove2me | solution 1 for WorkbookSource.plus_80996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:28.101418+00:00
-- url     : https://prove2.me/submissions/57eeef40-2e04-4b25-bad2-a9608ae9c0a1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c ≥ 1 / 3 * (13 - 4 * a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + a^5*c/27 + 4*a^4*b^2/27 - 4*a^4*b*c/27 + 4*a^4*c^2/27 + 2*a^3*b^3/9 - 17*a^3*b^2*c/27 - 17*a^3*b*c^2/27 + 2*a^3*c^3/9 + 4*a^2*b^4/27 - 17*a^2*b^3*c/27 + 22*a^2*b^2*c^2/9 - 17*a^2*b*c^3/27 + 4*a^2*c^4/27 + a*b^5/27 - 4*a*b^4*c/27 - 17*a*b^3*c^2/27 - 17*a*b^2*c^3/27 - 4*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + 4*b^4*c^2/27 + 2*b^3*c^3/9 + 4*b^2*c^4/27 + b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^4 * (b - a)^2 + (2/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^4 * (c - b)^2 + (58/27 : ℝ) * a^3 * (b - a)^3 + (29/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (19/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14/27 : ℝ) * a^3 * (c - b)^3 + (80/27 : ℝ) * a^2 * (b - a)^4 + (160/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (43/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (49/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14/27 : ℝ) * a^2 * (c - b)^4 + (56/27 : ℝ) * a^1 * (b - a)^5 + (140/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (142/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (73/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (19/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/27 : ℝ) * a^1 * (c - b)^5 + (16/27 : ℝ) * (b - a)^6 + (16/9 : ℝ) * (b - a)^5 * (c - b)^1 + (56/27 : ℝ) * (b - a)^4 * (c - b)^2 + (32/27 : ℝ) * (b - a)^3 * (c - b)^3 + (1/3 : ℝ) * (b - a)^2 * (c - b)^4 + (1/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + a^5*c/27 + 4*a^4*b^2/27 - 4*a^4*b*c/27 + 4*a^4*c^2/27 + 2*a^3*b^3/9 - 17*a^3*b^2*c/27 - 17*a^3*b*c^2/27 + 2*a^3*c^3/9 + 4*a^2*b^4/27 - 17*a^2*b^3*c/27 + 22*a^2*b^2*c^2/9 - 17*a^2*b*c^3/27 + 4*a^2*c^4/27 + a*b^5/27 - 4*a*b^4*c/27 - 17*a*b^3*c^2/27 - 17*a*b^2*c^3/27 - 4*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + 4*b^4*c^2/27 + 2*b^3*c^3/9 + 4*b^2*c^4/27 + b*c^5/27) := by
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
  have he : (4*a^2*b^2*c^2 - 13*a*b*c + 3*a*b + 3*a*c + 3*b*c) = (a^5*b/27 + a^5*c/27 + 4*a^4*b^2/27 - 4*a^4*b*c/27 + 4*a^4*c^2/27 + 2*a^3*b^3/9 - 17*a^3*b^2*c/27 - 17*a^3*b*c^2/27 + 2*a^3*c^3/9 + 4*a^2*b^4/27 - 17*a^2*b^3*c/27 + 22*a^2*b^2*c^2/9 - 17*a^2*b*c^3/27 + 4*a^2*c^4/27 + a*b^5/27 - 4*a*b^4*c/27 - 17*a*b^3*c^2/27 - 17*a*b^2*c^3/27 - 4*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + 4*b^4*c^2/27 + 2*b^3*c^3/9 + 4*b^2*c^4/27 + b*c^5/27) := by
    linear_combination (-a^4*b/27 - a^4*c/27 - a^3*b^2/9 + 2*a^3*b*c/9 - a^3*b/9 - a^3*c^2/9 - a^3*c/9 - a^2*b^3/9 + 14*a^2*b^2*c/27 - 2*a^2*b^2/9 + 14*a^2*b*c^2/27 + 8*a^2*b*c/9 - a^2*b/3 - a^2*c^3/9 - 2*a^2*c^2/9 - a^2*c/3 - a*b^4/27 + 2*a*b^3*c/9 - a*b^3/9 + 14*a*b^2*c^2/27 + 8*a*b^2*c/9 - a*b^2/3 + 2*a*b*c^3/9 + 8*a*b*c^2/9 + 10*a*b*c/3 - a*b - a*c^4/27 - a*c^3/9 - a*c^2/3 - a*c - b^4*c/27 - b^3*c^2/9 - b^3*c/9 - b^2*c^3/9 - 2*b^2*c^2/9 - b^2*c/3 - b*c^4/27 - b*c^3/9 - b*c^2/3 - b*c) * habc
  have hn : 0 ≤ (4*a^2*b^2*c^2 - 13*a*b*c + 3*a*b + 3*a*c + 3*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / a + 1 / b + 1 / c ≥ 1 / 3 * (13 - 4 * a * b * c)) := @solution
#print axioms solution
