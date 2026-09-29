-- Prove2me | solution 1 for WorkbookSource.plus_16317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:04.314476+00:00
-- url     : https://prove2.me/submissions/32437485-dee9-468c-a945-903f16ba73eb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b)/(b^2 + a) + (b^2 + c)/(c^2 + b) + (c^2 + a)/(a^2 + c) ≥ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 + 10*a^4*c^2/27 - 5*a^3*b^3/9 + 16*a^3*b^2*c/27 - a^3*b*c^2/3 - 5*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c/3 - 4*a^2*b^2*c^2/3 + 16*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 + 16*a*b^3*c^2/27 - a*b^2*c^3/3 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 - 5*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (b - a)^2 + (2 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^4 * (c - b)^2 + (5 : ℝ) * a^3 * (b - a)^3 + (8 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^3 * (c - b)^3 + (13/3 : ℝ) * a^2 * (b - a)^4 + (29/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (13 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (23/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4/3 : ℝ) * a^2 * (c - b)^4 + (41/27 : ℝ) * a^1 * (b - a)^5 + (125/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (203/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (166/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (55/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/27 : ℝ) * a^1 * (c - b)^5 + (5/27 : ℝ) * (b - a)^6 + (23/27 : ℝ) * (b - a)^5 * (c - b)^1 + (17/9 : ℝ) * (b - a)^4 * (c - b)^2 + (55/27 : ℝ) * (b - a)^3 * (c - b)^3 + (25/27 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 + 10*a^4*c^2/27 - 5*a^3*b^3/9 + 16*a^3*b^2*c/27 - a^3*b*c^2/3 - 5*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c/3 - 4*a^2*b^2*c^2/3 + 16*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 + 16*a*b^3*c^2/27 - a*b^2*c^3/3 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 - 5*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (c - a)^2 + (2 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^4 * (b - c)^2 + (5 : ℝ) * a^3 * (c - a)^3 + (7 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (8 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^3 * (b - c)^3 + (13/3 : ℝ) * a^2 * (c - a)^4 + (23/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (10 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (20/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4/3 : ℝ) * a^2 * (b - c)^4 + (41/27 : ℝ) * a^1 * (c - a)^5 + (80/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (113/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (103/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (37/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/27 : ℝ) * a^1 * (b - c)^5 + (5/27 : ℝ) * (c - a)^6 + (7/27 : ℝ) * (c - a)^5 * (b - c)^1 + (11/27 : ℝ) * (c - a)^4 * (b - c)^2 + (19/27 : ℝ) * (c - a)^3 * (b - c)^3 + (11/27 : ℝ) * (c - a)^2 * (b - c)^4 + (1/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 + 10*a^4*c^2/27 - 5*a^3*b^3/9 + 16*a^3*b^2*c/27 - a^3*b*c^2/3 - 5*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c/3 - 4*a^2*b^2*c^2/3 + 16*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 + 16*a*b^3*c^2/27 - a*b^2*c^3/3 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 - 5*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
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
  have he : (a^4*b + a^4*c^2 + a^3*b^2 - 3*a^3*b - 3*a^3*c^2 + a^3*c + a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2*c^2 + a^2*b^2*c + a^2*b^2 + a^2*b*c^2 + a^2*b*c + a^2*b + a^2*c^3 + a^2*c^2 + a*b^3 + a*b^2*c^2 + a*b^2*c + a*b*c^2 - 3*a*b*c + a*c^4 - 3*a*c^3 + a*c^2 + b^4*c + b^3*c^2 - 3*b^3*c + b^2*c^4 - 3*b^2*c^3 + b^2*c^2 + b^2*c + b*c^3) = (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 + 10*a^4*c^2/27 - 5*a^3*b^3/9 + 16*a^3*b^2*c/27 - a^3*b*c^2/3 - 5*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c/3 - 4*a^2*b^2*c^2/3 + 16*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 + 16*a*b^3*c^2/27 - a*b^2*c^3/3 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 - 5*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    linear_combination (-a^4*b/27 - a^4*c/9 - 5*a^3*b^2/27 + 4*a^3*b*c/27 + 8*a^3*b/9 + 20*a^3*c^2/27 - a^3*c/3 + 20*a^2*b^3/27 - 5*a^2*b^2*c/9 - 4*a^2*b^2/9 - 5*a^2*b*c^2/9 - a^2*b*c/9 - a^2*b/3 - 5*a^2*c^3/27 - 4*a^2*c^2/9 - a*b^4/9 + 4*a*b^3*c/27 - a*b^3/3 - 5*a*b^2*c^2/9 - a*b^2*c/9 + 4*a*b*c^3/27 - a*b*c^2/9 + a*b*c - a*c^4/27 + 8*a*c^3/9 - a*c^2/3 - b^4*c/27 - 5*b^3*c^2/27 + 8*b^3*c/9 + 20*b^2*c^3/27 - 4*b^2*c^2/9 - b^2*c/3 - b*c^4/9 - b*c^3/3) * hab
  have hn : 0 ≤ (a^4*b + a^4*c^2 + a^3*b^2 - 3*a^3*b - 3*a^3*c^2 + a^3*c + a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2*c^2 + a^2*b^2*c + a^2*b^2 + a^2*b*c^2 + a^2*b*c + a^2*b + a^2*c^3 + a^2*c^2 + a*b^3 + a*b^2*c^2 + a*b^2*c + a*b*c^2 - 3*a*b*c + a*c^4 - 3*a*c^3 + a*c^2 + b^4*c + b^3*c^2 - 3*b^3*c + b^2*c^4 - 3*b^2*c^3 + b^2*c^2 + b^2*c + b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 + b)/(b^2 + a) + (b^2 + c)/(c^2 + b) + (c^2 + a)/(a^2 + c) ≥ 3) := @solution
#print axioms solution
