-- Prove2me | solution 1 for WorkbookSource.base_2864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:16.866828+00:00
-- url     : https://prove2.me/submissions/50680d5e-7c4b-4160-b51d-88a0b7511137

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^3 / (a^2 + b * c + c * a) + b^3 / (b^2 + c * a + a * b) + c^3 / (c^2 + a * b + b * c) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b^2/3 + 2*a^5*b*c/3 + a^4*b^3/3 - a^4*b^2*c/3 + 2*a^4*b*c^2/3 + 2*a^4*c^3/3 + 2*a^3*b^4/3 - a^3*b^3*c - 5*a^3*b^2*c^2/3 - a^3*b*c^3 + a^3*c^4/3 + 2*a^2*b^4*c/3 - 5*a^2*b^3*c^2/3 - 5*a^2*b^2*c^3/3 - a^2*b*c^4/3 + 2*a^2*c^5/3 + 2*a*b^5*c/3 - a*b^4*c^2/3 - a*b^3*c^3 + 2*a*b^2*c^4/3 + 2*a*b*c^5/3 + 2*b^5*c^2/3 + b^4*c^3/3 + 2*b^3*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^5 * (b - a)^2 + (11 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (11 : ℝ) * a^5 * (c - b)^2 + (39 : ℝ) * a^4 * (b - a)^3 + (56 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (49 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^4 * (c - b)^3 + (54 : ℝ) * a^3 * (b - a)^4 + (304/3 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (92 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (134/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^3 * (c - b)^4 + (110/3 : ℝ) * a^2 * (b - a)^5 + (253/3 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (84 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (140/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (13 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (4/3 : ℝ) * a^2 * (c - b)^5 + (37/3 : ℝ) * a^1 * (b - a)^6 + (33 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (107/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (61/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (5/3 : ℝ) * (b - a)^7 + (5 : ℝ) * (b - a)^6 * (c - b)^1 + (17/3 : ℝ) * (b - a)^5 * (c - b)^2 + (3 : ℝ) * (b - a)^4 * (c - b)^3 + (2/3 : ℝ) * (b - a)^3 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*b^2/3 + 2*a^5*b*c/3 + a^4*b^3/3 - a^4*b^2*c/3 + 2*a^4*b*c^2/3 + 2*a^4*c^3/3 + 2*a^3*b^4/3 - a^3*b^3*c - 5*a^3*b^2*c^2/3 - a^3*b*c^3 + a^3*c^4/3 + 2*a^2*b^4*c/3 - 5*a^2*b^3*c^2/3 - 5*a^2*b^2*c^3/3 - a^2*b*c^4/3 + 2*a^2*c^5/3 + 2*a*b^5*c/3 - a*b^4*c^2/3 - a*b^3*c^3 + 2*a*b^2*c^4/3 + 2*a*b*c^5/3 + 2*b^5*c^2/3 + b^4*c^3/3 + 2*b^3*c^4/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^5 * (c - a)^2 + (11 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (11 : ℝ) * a^5 * (b - c)^2 + (39 : ℝ) * a^4 * (c - a)^3 + (61 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (54 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (16 : ℝ) * a^4 * (b - c)^3 + (54 : ℝ) * a^3 * (c - a)^4 + (344/3 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (112 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (154/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (8 : ℝ) * a^3 * (b - c)^4 + (110/3 : ℝ) * a^2 * (c - a)^5 + (99 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (340/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (66 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (53/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (4/3 : ℝ) * a^2 * (b - c)^5 + (37/3 : ℝ) * a^1 * (c - a)^6 + (41 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (167/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (39 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (14 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (5/3 : ℝ) * (c - a)^7 + (20/3 : ℝ) * (c - a)^6 * (b - c)^1 + (32/3 : ℝ) * (c - a)^5 * (b - c)^2 + (26/3 : ℝ) * (c - a)^4 * (b - c)^3 + (11/3 : ℝ) * (c - a)^3 * (b - c)^4 + (2/3 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b^2/3 + 2*a^5*b*c/3 + a^4*b^3/3 - a^4*b^2*c/3 + 2*a^4*b*c^2/3 + 2*a^4*c^3/3 + 2*a^3*b^4/3 - a^3*b^3*c - 5*a^3*b^2*c^2/3 - a^3*b*c^3 + a^3*c^4/3 + 2*a^2*b^4*c/3 - 5*a^2*b^3*c^2/3 - 5*a^2*b^2*c^3/3 - a^2*b*c^4/3 + 2*a^2*c^5/3 + 2*a*b^5*c/3 - a*b^4*c^2/3 - a*b^3*c^3 + 2*a*b^2*c^4/3 + 2*a*b*c^5/3 + 2*b^5*c^2/3 + b^4*c^3/3 + 2*b^3*c^4/3) := by
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
  have he : (a^5*b^2 + a^5*b*c + a^4*b^3 + a^4*b^2*c - a^4*b^2 + 2*a^4*b*c^2 - a^4*b*c + a^4*c^3 + a^3*b^4 + a^3*b^3*c - a^3*b^3 + a^3*b^2*c^2 - 2*a^3*b^2*c + a^3*b*c^3 - 3*a^3*b*c^2 + a^3*c^4 - a^3*c^3 + 2*a^2*b^4*c + a^2*b^3*c^2 - 3*a^2*b^3*c + a^2*b^2*c^3 - 3*a^2*b^2*c^2 + a^2*b*c^4 - 2*a^2*b*c^3 + a^2*c^5 - a^2*c^4 + a*b^5*c + a*b^4*c^2 - a*b^4*c + a*b^3*c^3 - 2*a*b^3*c^2 + 2*a*b^2*c^4 - 3*a*b^2*c^3 + a*b*c^5 - a*b*c^4 + b^5*c^2 + b^4*c^3 - b^4*c^2 + b^3*c^4 - b^3*c^3) = (2*a^5*b^2/3 + 2*a^5*b*c/3 + a^4*b^3/3 - a^4*b^2*c/3 + 2*a^4*b*c^2/3 + 2*a^4*c^3/3 + 2*a^3*b^4/3 - a^3*b^3*c - 5*a^3*b^2*c^2/3 - a^3*b*c^3 + a^3*c^4/3 + 2*a^2*b^4*c/3 - 5*a^2*b^3*c^2/3 - 5*a^2*b^2*c^3/3 - a^2*b*c^4/3 + 2*a^2*c^5/3 + 2*a*b^5*c/3 - a*b^4*c^2/3 - a*b^3*c^3 + 2*a*b^2*c^4/3 + 2*a*b*c^5/3 + 2*b^5*c^2/3 + b^4*c^3/3 + 2*b^3*c^4/3) := by
    linear_combination (a^4*b^2/3 + a^4*b*c/3 + a^3*b^3/3 + 2*a^3*b^2*c/3 + a^3*b*c^2 + a^3*c^3/3 + a^2*b^3*c + a^2*b^2*c^2 + 2*a^2*b*c^3/3 + a^2*c^4/3 + a*b^4*c/3 + 2*a*b^3*c^2/3 + a*b^2*c^3 + a*b*c^4/3 + b^4*c^2/3 + b^3*c^3/3) * habc
  have hn : 0 ≤ (a^5*b^2 + a^5*b*c + a^4*b^3 + a^4*b^2*c - a^4*b^2 + 2*a^4*b*c^2 - a^4*b*c + a^4*c^3 + a^3*b^4 + a^3*b^3*c - a^3*b^3 + a^3*b^2*c^2 - 2*a^3*b^2*c + a^3*b*c^3 - 3*a^3*b*c^2 + a^3*c^4 - a^3*c^3 + 2*a^2*b^4*c + a^2*b^3*c^2 - 3*a^2*b^3*c + a^2*b^2*c^3 - 3*a^2*b^2*c^2 + a^2*b*c^4 - 2*a^2*b*c^3 + a^2*c^5 - a^2*c^4 + a*b^5*c + a*b^4*c^2 - a*b^4*c + a*b^3*c^3 - 2*a*b^3*c^2 + 2*a*b^2*c^4 - 3*a*b^2*c^3 + a*b*c^5 - a*b*c^4 + b^5*c^2 + b^4*c^3 - b^4*c^2 + b^3*c^4 - b^3*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^3 / (a^2 + b * c + c * a) + b^3 / (b^2 + c * a + a * b) + c^3 / (c^2 + a * b + b * c) ≥ 1) := @solution
#print axioms solution
