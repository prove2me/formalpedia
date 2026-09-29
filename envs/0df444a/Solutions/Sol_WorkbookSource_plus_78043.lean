-- Prove2me | solution 1 for WorkbookSource.plus_78043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:32.621593+00:00
-- url     : https://prove2.me/submissions/dfc934cd-4dd8-4493-85ad-5a9835aa44fa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 + 3 ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - 5*a^4*b^2*c^2/3 + a^3*b^5/3 + 2*a^3*b^3*c^2/3 + 2*a^3*b^2*c^3/3 + a^2*b^6/3 + a^2*b^5*c/3 - 5*a^2*b^4*c^2/3 + 2*a^2*b^3*c^3/3 - 5*a^2*b^2*c^4/3 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (14/3 : ℝ) * a^6 * (b - a)^2 + (14/3 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (14/3 : ℝ) * a^6 * (c - b)^2 + (59/3 : ℝ) * a^5 * (b - a)^3 + (37 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (34 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (25/3 : ℝ) * a^5 * (c - b)^3 + (35 : ℝ) * a^4 * (b - a)^4 + (95 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (320/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (140/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (20/3 : ℝ) * a^4 * (c - b)^4 + (34 : ℝ) * a^3 * (b - a)^5 + (355/3 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (164 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (308/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (85/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8/3 : ℝ) * a^3 * (c - b)^5 + (19 : ℝ) * a^2 * (b - a)^6 + (238/3 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (132 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (322/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (130/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (23/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1/3 : ℝ) * a^2 * (c - b)^6 + (17/3 : ℝ) * a^1 * (b - a)^7 + (82/3 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (160/3 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (160/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (85/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (22/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2/3 : ℝ) * (b - a)^8 + (11/3 : ℝ) * (b - a)^7 * (c - b)^1 + (25/3 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (20/3 : ℝ) * (b - a)^4 * (c - b)^4 + (7/3 : ℝ) * (b - a)^3 * (c - b)^5 + (1/3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - 5*a^4*b^2*c^2/3 + a^3*b^5/3 + 2*a^3*b^3*c^2/3 + 2*a^3*b^2*c^3/3 + a^2*b^6/3 + a^2*b^5*c/3 - 5*a^2*b^4*c^2/3 + 2*a^2*b^3*c^3/3 - 5*a^2*b^2*c^4/3 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (14/3 : ℝ) * a^6 * (c - a)^2 + (14/3 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (14/3 : ℝ) * a^6 * (b - c)^2 + (59/3 : ℝ) * a^5 * (c - a)^3 + (22 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (19 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (25/3 : ℝ) * a^5 * (b - c)^3 + (35 : ℝ) * a^4 * (c - a)^4 + (45 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (95/3 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (65/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (20/3 : ℝ) * a^4 * (b - c)^4 + (34 : ℝ) * a^3 * (c - a)^5 + (155/3 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (92/3 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (58/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (35/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (8/3 : ℝ) * a^3 * (b - c)^5 + (19 : ℝ) * a^2 * (c - a)^6 + (104/3 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (61/3 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (22/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (5 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (7/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1/3 : ℝ) * a^2 * (b - c)^6 + (17/3 : ℝ) * a^1 * (c - a)^7 + (37/3 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (25/3 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (5/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (2/3 : ℝ) * (c - a)^8 + (5/3 : ℝ) * (c - a)^7 * (b - c)^1 + (4/3 : ℝ) * (c - a)^6 * (b - c)^2 + (1/3 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - 5*a^4*b^2*c^2/3 + a^3*b^5/3 + 2*a^3*b^3*c^2/3 + 2*a^3*b^2*c^3/3 + a^2*b^6/3 + a^2*b^5*c/3 - 5*a^2*b^4*c^2/3 + 2*a^2*b^3*c^3/3 - 5*a^2*b^2*c^4/3 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
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
  have he : (a^5*c^2 - 2*a^4*b^2*c^2 + a^2*b^5 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + b^2*c^5) = (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - 5*a^4*b^2*c^2/3 + a^3*b^5/3 + 2*a^3*b^3*c^2/3 + 2*a^3*b^2*c^3/3 + a^2*b^6/3 + a^2*b^5*c/3 - 5*a^2*b^4*c^2/3 + 2*a^2*b^3*c^3/3 - 5*a^2*b^2*c^4/3 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    linear_combination (-a^5*c^2/3 - a^3*b^2*c^2/3 - a^2*b^5/3 - a^2*b^3*c^2/3 - a^2*b^2*c^3/3 - a^2*b^2*c^2 - b^2*c^5/3) * habc
  have hn : 0 ≤ (a^5*c^2 - 2*a^4*b^2*c^2 + a^2*b^5 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + b^2*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a ^ 3 / b ^ 2 + b ^ 3 / c ^ 2 + c ^ 3 / a ^ 2 + 3 ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
