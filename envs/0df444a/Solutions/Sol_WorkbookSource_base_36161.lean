-- Prove2me | solution 1 for WorkbookSource.base_36161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:28.59508+00:00
-- url     : https://prove2.me/submissions/7d05b5da-2d78-4d20-b390-eb80ff6da208

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / b^2 + b^3 / c^2 + c^3 / a^2 ≥ a^2 + b^2 + c^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - a^4*b^2*c^2 + a^3*b^5/3 + a^2*b^6/3 + a^2*b^5*c/3 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^6 * (b - a)^2 + (16/3 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^6 * (c - b)^2 + (67/3 : ℝ) * a^5 * (b - a)^3 + (41 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (38 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (29/3 : ℝ) * a^5 * (c - b)^3 + (39 : ℝ) * a^4 * (b - a)^4 + (103 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (346/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (154/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (22/3 : ℝ) * a^4 * (c - b)^4 + (110/3 : ℝ) * a^3 * (b - a)^5 + (125 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (172 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (108 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (89/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8/3 : ℝ) * a^3 * (c - b)^5 + (59/3 : ℝ) * a^2 * (b - a)^6 + (244/3 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (404/3 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (328/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (44 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (23/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1/3 : ℝ) * a^2 * (c - b)^6 + (17/3 : ℝ) * a^1 * (b - a)^7 + (82/3 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (160/3 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (160/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (85/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (22/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2/3 : ℝ) * (b - a)^8 + (11/3 : ℝ) * (b - a)^7 * (c - b)^1 + (25/3 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (20/3 : ℝ) * (b - a)^4 * (c - b)^4 + (7/3 : ℝ) * (b - a)^3 * (c - b)^5 + (1/3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - a^4*b^2*c^2 + a^3*b^5/3 + a^2*b^6/3 + a^2*b^5*c/3 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^6 * (c - a)^2 + (16/3 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (16/3 : ℝ) * a^6 * (b - c)^2 + (67/3 : ℝ) * a^5 * (c - a)^3 + (26 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (23 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (29/3 : ℝ) * a^5 * (b - c)^3 + (39 : ℝ) * a^4 * (c - a)^4 + (53 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (121/3 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (79/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (22/3 : ℝ) * a^4 * (b - c)^4 + (110/3 : ℝ) * a^3 * (c - a)^5 + (175/3 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (116/3 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (74/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (13 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (8/3 : ℝ) * a^3 * (b - c)^5 + (59/3 : ℝ) * a^2 * (c - a)^6 + (110/3 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (23 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (28/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (17/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (7/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1/3 : ℝ) * a^2 * (b - c)^6 + (17/3 : ℝ) * a^1 * (c - a)^7 + (37/3 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (25/3 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (5/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (2/3 : ℝ) * (c - a)^8 + (5/3 : ℝ) * (c - a)^7 * (b - c)^1 + (4/3 : ℝ) * (c - a)^6 * (b - c)^2 + (1/3 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - a^4*b^2*c^2 + a^3*b^5/3 + a^2*b^6/3 + a^2*b^5*c/3 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
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
  have he : (a^5*c^2 - a^4*b^2*c^2 + a^2*b^5 - a^2*b^4*c^2 - a^2*b^2*c^4 + b^2*c^5) = (a^6*c^2/3 + a^5*b*c^2/3 + a^5*c^3/3 - a^4*b^2*c^2 + a^3*b^5/3 + a^2*b^6/3 + a^2*b^5*c/3 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*b^2*c^5/3 + b^3*c^5/3 + b^2*c^6/3) := by
    linear_combination (-a^5*c^2/3 - a^2*b^5/3 - b^2*c^5/3) * hab
  have hn : 0 ≤ (a^5*c^2 - a^4*b^2*c^2 + a^2*b^5 - a^2*b^4*c^2 - a^2*b^2*c^4 + b^2*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^3 / b^2 + b^3 / c^2 + c^3 / a^2 ≥ a^2 + b^2 + c^2) := @solution
#print axioms solution
