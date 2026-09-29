-- Prove2me | solution 1 for WorkbookSource.base_5494
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:39.894886+00:00
-- url     : https://prove2.me/submissions/428aeb26-44a1-477a-951e-e1f1ed574597

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a - b * c) / (b * (1 + c)) + (b - c * a) / (c * (1 + a)) + (c - a * b) / (a * (1 + b)) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*c/27 + a^4*b^2/27 + 2*a^4*b*c/3 + a^4*c^2/3 + 2*a^3*b^3/9 + 4*a^3*b*c^2/27 + 2*a^3*c^3/9 + a^2*b^4/3 + 4*a^2*b^3*c/27 - 14*a^2*b^2*c^2/3 + a^2*c^4/27 + 4*a*b^5/27 + 2*a*b^4*c/3 + 4*a*b^2*c^3/27 + 2*a*b*c^4/3 + b^4*c^2/27 + 2*b^3*c^3/9 + b^2*c^4/3 + 4*b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (136/9 : ℝ) * a^3 * (b - a)^3 + (74/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (22 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (56/9 : ℝ) * a^3 * (c - b)^3 + (136/9 : ℝ) * a^2 * (b - a)^4 + (308/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (34 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (134/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (16/9 : ℝ) * a^2 * (c - b)^4 + (164/27 : ℝ) * a^1 * (b - a)^5 + (482/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (572/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (322/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (76/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/27 : ℝ) * a^1 * (c - b)^5 + (20/27 : ℝ) * (b - a)^6 + (76/27 : ℝ) * (b - a)^5 * (c - b)^1 + (113/27 : ℝ) * (b - a)^4 * (c - b)^2 + (82/27 : ℝ) * (b - a)^3 * (c - b)^3 + (29/27 : ℝ) * (b - a)^2 * (c - b)^4 + (4/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*c/27 + a^4*b^2/27 + 2*a^4*b*c/3 + a^4*c^2/3 + 2*a^3*b^3/9 + 4*a^3*b*c^2/27 + 2*a^3*c^3/9 + a^2*b^4/3 + 4*a^2*b^3*c/27 - 14*a^2*b^2*c^2/3 + a^2*c^4/27 + 4*a*b^5/27 + 2*a*b^4*c/3 + 4*a*b^2*c^3/27 + 2*a*b*c^4/3 + b^4*c^2/27 + 2*b^3*c^3/9 + b^2*c^4/3 + 4*b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (c - a)^2 + (16/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16/3 : ℝ) * a^4 * (b - c)^2 + (136/9 : ℝ) * a^3 * (c - a)^3 + (62/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (18 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (56/9 : ℝ) * a^3 * (b - c)^3 + (136/9 : ℝ) * a^2 * (c - a)^4 + (236/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (22 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (98/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (16/9 : ℝ) * a^2 * (b - c)^4 + (164/27 : ℝ) * a^1 * (c - a)^5 + (338/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (284/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (142/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (40/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/27 : ℝ) * a^1 * (b - c)^5 + (20/27 : ℝ) * (c - a)^6 + (44/27 : ℝ) * (c - a)^5 * (b - c)^1 + (11/9 : ℝ) * (c - a)^4 * (b - c)^2 + (10/27 : ℝ) * (c - a)^3 * (b - c)^3 + (1/27 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*c/27 + a^4*b^2/27 + 2*a^4*b*c/3 + a^4*c^2/3 + 2*a^3*b^3/9 + 4*a^3*b*c^2/27 + 2*a^3*c^3/9 + a^2*b^4/3 + 4*a^2*b^3*c/27 - 14*a^2*b^2*c^2/3 + a^2*c^4/27 + 4*a*b^5/27 + 2*a*b^4*c/3 + 4*a*b^2*c^3/27 + 2*a*b*c^4/3 + b^4*c^2/27 + 2*b^3*c^3/9 + b^2*c^4/3 + 4*b*c^5/27) := by
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
  have he : (a^3*b*c + a^3*c - 3*a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 + a^2*c + a*b^3*c + a*b^3 - 2*a*b^2*c^2 + a*b^2 + a*b*c^3 + b*c^3 + b*c^2) = (4*a^5*c/27 + a^4*b^2/27 + 2*a^4*b*c/3 + a^4*c^2/3 + 2*a^3*b^3/9 + 4*a^3*b*c^2/27 + 2*a^3*c^3/9 + a^2*b^4/3 + 4*a^2*b^3*c/27 - 14*a^2*b^2*c^2/3 + a^2*c^4/27 + 4*a*b^5/27 + 2*a*b^4*c/3 + 4*a*b^2*c^3/27 + 2*a*b*c^4/3 + b^4*c^2/27 + 2*b^3*c^3/9 + b^2*c^4/3 + 4*b*c^5/27) := by
    linear_combination (-4*a^4*c/27 - a^3*b^2/27 - 14*a^3*b*c/27 - 5*a^3*c^2/27 - 4*a^3*c/9 - 5*a^2*b^3/27 + 5*a^2*b^2*c/9 - a^2*b^2/9 + 5*a^2*b*c^2/9 - a^2*b*c/9 - a^2*c^3/27 - a^2*c^2/9 - a^2*c/3 - 4*a*b^4/27 - 14*a*b^3*c/27 - 4*a*b^3/9 + 5*a*b^2*c^2/9 - a*b^2*c/9 - a*b^2/3 - 14*a*b*c^3/27 - a*b*c^2/9 - b^3*c^2/27 - 5*b^2*c^3/27 - b^2*c^2/9 - 4*b*c^4/27 - 4*b*c^3/9 - b*c^2/3) * hab
  have hn : 0 ≤ (a^3*b*c + a^3*c - 3*a^2*b^2*c^2 - 2*a^2*b^2*c - 2*a^2*b*c^2 + a^2*c + a*b^3*c + a*b^3 - 2*a*b^2*c^2 + a*b^2 + a*b*c^3 + b*c^3 + b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a - b * c) / (b * (1 + c)) + (b - c * a) / (c * (1 + a)) + (c - a * b) / (a * (1 + b)) ≥ 0) := @solution
#print axioms solution
