-- Prove2me | solution 1 for WorkbookSource.base_21549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:11.028584+00:00
-- url     : https://prove2.me/submissions/1275e220-74fc-442c-8fce-09b462fe863b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (3 * a + b ^ 2) + b / (3 * b + c ^ 2) + c / (3 * c + a ^ 2) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/3 + 2*a^4*b^2/3 - a^4*b*c/3 + 5*a^4*c^2/3 + 2*a^3*b^3 - 7*a^3*b^2*c/3 - a^3*b*c^2 + 2*a^3*c^3 + 5*a^2*b^4/3 - a^2*b^3*c - 3*a^2*b^2*c^2 - 7*a^2*b*c^3/3 + 2*a^2*c^4/3 - a*b^4*c/3 - 7*a*b^3*c^2/3 - a*b^2*c^3 - a*b*c^4/3 + a*c^5/3 + b^5*c/3 + 2*b^4*c^2/3 + 2*b^3*c^3 + 5*b^2*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40/3 : ℝ) * a^4 * (b - a)^2 + (40/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (40/3 : ℝ) * a^4 * (c - b)^2 + (124/3 : ℝ) * a^3 * (b - a)^3 + (65 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (143/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^3 + (143/3 : ℝ) * a^2 * (b - a)^4 + (304/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (82 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (85/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (11/3 : ℝ) * a^2 * (c - b)^4 + (73/3 : ℝ) * a^1 * (b - a)^5 + (64 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (188/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/3 : ℝ) * a^1 * (c - b)^5 + (14/3 : ℝ) * (b - a)^6 + (43/3 : ℝ) * (b - a)^5 * (c - b)^1 + (50/3 : ℝ) * (b - a)^4 * (c - b)^2 + (26/3 : ℝ) * (b - a)^3 * (c - b)^3 + (5/3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/3 + 2*a^4*b^2/3 - a^4*b*c/3 + 5*a^4*c^2/3 + 2*a^3*b^3 - 7*a^3*b^2*c/3 - a^3*b*c^2 + 2*a^3*c^3 + 5*a^2*b^4/3 - a^2*b^3*c - 3*a^2*b^2*c^2 - 7*a^2*b*c^3/3 + 2*a^2*c^4/3 - a*b^4*c/3 - 7*a*b^3*c^2/3 - a*b^2*c^3 - a*b*c^4/3 + a*c^5/3 + b^5*c/3 + 2*b^4*c^2/3 + 2*b^3*c^3 + 5*b^2*c^4/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40/3 : ℝ) * a^4 * (c - a)^2 + (40/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (40/3 : ℝ) * a^4 * (b - c)^2 + (124/3 : ℝ) * a^3 * (c - a)^3 + (59 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (125/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^3 * (b - c)^3 + (143/3 : ℝ) * a^2 * (c - a)^4 + (268/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (64 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (67/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (11/3 : ℝ) * a^2 * (b - c)^4 + (73/3 : ℝ) * a^1 * (c - a)^5 + (173/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (50 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (61/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (13/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/3 : ℝ) * a^1 * (b - c)^5 + (14/3 : ℝ) * (c - a)^6 + (41/3 : ℝ) * (c - a)^5 * (b - c)^1 + (15 : ℝ) * (c - a)^4 * (b - c)^2 + (8 : ℝ) * (c - a)^3 * (b - c)^3 + (7/3 : ℝ) * (c - a)^2 * (b - c)^4 + (1/3 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/3 + 2*a^4*b^2/3 - a^4*b*c/3 + 5*a^4*c^2/3 + 2*a^3*b^3 - 7*a^3*b^2*c/3 - a^3*b*c^2 + 2*a^3*c^3 + 5*a^2*b^4/3 - a^2*b^3*c - 3*a^2*b^2*c^2 - 7*a^2*b*c^3/3 + 2*a^2*c^4/3 - a*b^4*c/3 - 7*a*b^3*c^2/3 - a*b^2*c^3 - a*b*c^4/3 + a*c^5/3 + b^5*c/3 + 2*b^4*c^2/3 + 2*b^3*c^3 + 5*b^2*c^4/3) := by
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
  have he : (3*a^3*b + 5*a^3*c^2 + 5*a^2*b^3 + 3*a^2*b^2*c^2 - 27*a*b*c + 3*a*c^3 + 3*b^3*c + 5*b^2*c^3) = (a^5*b/3 + 2*a^4*b^2/3 - a^4*b*c/3 + 5*a^4*c^2/3 + 2*a^3*b^3 - 7*a^3*b^2*c/3 - a^3*b*c^2 + 2*a^3*c^3 + 5*a^2*b^4/3 - a^2*b^3*c - 3*a^2*b^2*c^2 - 7*a^2*b*c^3/3 + 2*a^2*c^4/3 - a*b^4*c/3 - 7*a*b^3*c^2/3 - a*b^2*c^3 - a*b*c^4/3 + a*c^5/3 + b^5*c/3 + 2*b^4*c^2/3 + 2*b^3*c^3 + 5*b^2*c^4/3) := by
    linear_combination (-a^4*b/3 - a^3*b^2/3 + 2*a^3*b*c/3 - a^3*b - 5*a^3*c^2/3 - 5*a^2*b^3/3 + 2*a^2*b^2*c + 2*a^2*b*c^2 + 3*a^2*b*c - a^2*c^3/3 + 2*a*b^3*c/3 + 2*a*b^2*c^2 + 3*a*b^2*c + 2*a*b*c^3/3 + 3*a*b*c^2 + 9*a*b*c - a*c^4/3 - a*c^3 - b^4*c/3 - b^3*c^2/3 - b^3*c - 5*b^2*c^3/3) * hab
  have hn : 0 ≤ (3*a^3*b + 5*a^3*c^2 + 5*a^2*b^3 + 3*a^2*b^2*c^2 - 27*a*b*c + 3*a*c^3 + 3*b^3*c + 5*b^2*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (3 * a + b ^ 2) + b / (3 * b + c ^ 2) + c / (3 * c + a ^ 2) ≤ 3 / 4) := @solution
#print axioms solution
