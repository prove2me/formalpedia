-- Prove2me | solution 1 for WorkbookSource.plus_72154
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:21.761404+00:00
-- url     : https://prove2.me/submissions/1ef95b46-57b1-4cdd-ab2d-1e0cb68b4a6c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 / b + b^3 / c + c^3 / a) ≥ 3 / 2 * (3 - a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c/3 + a^4*b*c/3 + 2*a^4*c^2/3 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4/3 - a^2*b^3*c + a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4/3 + 2*b^2*c^4/3 + 2*b*c^5/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (19/3 : ℝ) * a^4 * (b - a)^2 + (19/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (19/3 : ℝ) * a^4 * (c - b)^2 + (50/3 : ℝ) * a^3 * (b - a)^3 + (31 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (95/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (26/3 : ℝ) * a^3 * (c - b)^3 + (49/3 : ℝ) * a^2 * (b - a)^4 + (134/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (56 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (83/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (13/3 : ℝ) * a^2 * (c - b)^4 + (22/3 : ℝ) * a^1 * (b - a)^5 + (80/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (122/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (85/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (25/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/3 : ℝ) * a^1 * (c - b)^5 + (4/3 : ℝ) * (b - a)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (32/3 : ℝ) * (b - a)^4 * (c - b)^2 + (28/3 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 + (2/3 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c/3 + a^4*b*c/3 + 2*a^4*c^2/3 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4/3 - a^2*b^3*c + a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4/3 + 2*b^2*c^4/3 + 2*b*c^5/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (19/3 : ℝ) * a^4 * (c - a)^2 + (19/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (19/3 : ℝ) * a^4 * (b - c)^2 + (50/3 : ℝ) * a^3 * (c - a)^3 + (19 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (59/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (26/3 : ℝ) * a^3 * (b - c)^3 + (49/3 : ℝ) * a^2 * (c - a)^4 + (62/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (20 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (47/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (13/3 : ℝ) * a^2 * (b - c)^4 + (22/3 : ℝ) * a^1 * (c - a)^5 + (10 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (22/3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (7 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (11/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2/3 : ℝ) * a^1 * (b - c)^5 + (4/3 : ℝ) * (c - a)^6 + (2 : ℝ) * (c - a)^5 * (b - c)^1 + (2/3 : ℝ) * (c - a)^4 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c/3 + a^4*b*c/3 + 2*a^4*c^2/3 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4/3 - a^2*b^3*c + a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4/3 + 2*b^2*c^4/3 + 2*b*c^5/3) := by
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
  have he : (2*a^4*c + 3*a^2*b^2*c^2 + 2*a*b^4 - 9*a*b*c + 2*b*c^4) = (2*a^5*c/3 + a^4*b*c/3 + 2*a^4*c^2/3 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4/3 - a^2*b^3*c + a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4/3 + 2*b^2*c^4/3 + 2*b*c^5/3) := by
    linear_combination (-2*a^4*c/3 + a^3*b*c/3 + 2*a^2*b^2*c/3 + 2*a^2*b*c^2/3 + a^2*b*c - 2*a*b^4/3 + a*b^3*c/3 + 2*a*b^2*c^2/3 + a*b^2*c + a*b*c^3/3 + a*b*c^2 + 3*a*b*c - 2*b*c^4/3) * habc
  have hn : 0 ≤ (2*a^4*c + 3*a^2*b^2*c^2 + 2*a*b^4 - 9*a*b*c + 2*b*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^3 / b + b^3 / c + c^3 / a) ≥ 3 / 2 * (3 - a * b * c)) := @solution
#print axioms solution
