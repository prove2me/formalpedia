-- Prove2me | solution 1 for WorkbookSource.base_25410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:26.282223+00:00
-- url     : https://prove2.me/submissions/d43f236c-3391-40b6-a381-6f454f6c1af8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + b)/(a^2 + 1) + (b^2 + c)/(b^2 + 1) + (c^2 + a)/(c^2 + 1) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5/27 + a^4*c/9 + 16*a^3*b^2/27 - 8*a^3*c^2/27 - 8*a^2*b^3/27 - 4*a^2*b^2*c/9 - 4*a^2*b*c^2/9 + 16*a^2*c^3/27 + a*b^4/9 - 4*a*b^2*c^2/9 + b^5/27 + 16*b^3*c^2/27 - 8*b^2*c^3/27 + b*c^4/9 + c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^3 * (b - a)^2 + (4/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (4/3 : ℝ) * a^3 * (c - b)^2 + (26/9 : ℝ) * a^2 * (b - a)^3 + (10/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (8/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (10/9 : ℝ) * a^2 * (c - b)^3 + (56/27 : ℝ) * a^1 * (b - a)^4 + (76/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (16/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (28/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (8/27 : ℝ) * a^1 * (c - b)^4 + (13/27 : ℝ) * (b - a)^5 + (25/27 : ℝ) * (b - a)^4 * (c - b)^1 + (20/27 : ℝ) * (b - a)^3 * (c - b)^2 + (14/27 : ℝ) * (b - a)^2 * (c - b)^3 + (8/27 : ℝ) * (b - a)^1 * (c - b)^4 + (1/27 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5/27 + a^4*c/9 + 16*a^3*b^2/27 - 8*a^3*c^2/27 - 8*a^2*b^3/27 - 4*a^2*b^2*c/9 - 4*a^2*b*c^2/9 + 16*a^2*c^3/27 + a*b^4/9 - 4*a*b^2*c^2/9 + b^5/27 + 16*b^3*c^2/27 - 8*b^2*c^3/27 + b*c^4/9 + c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^3 * (c - a)^2 + (4/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (4/3 : ℝ) * a^3 * (b - c)^2 + (26/9 : ℝ) * a^2 * (c - a)^3 + (16/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (14/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (10/9 : ℝ) * a^2 * (b - c)^3 + (56/27 : ℝ) * a^1 * (c - a)^4 + (148/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (52/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (64/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (8/27 : ℝ) * a^1 * (b - c)^4 + (13/27 : ℝ) * (c - a)^5 + (40/27 : ℝ) * (c - a)^4 * (b - c)^1 + (50/27 : ℝ) * (c - a)^3 * (b - c)^2 + (26/27 : ℝ) * (c - a)^2 * (b - c)^3 + (5/27 : ℝ) * (c - a)^1 * (b - c)^4 + (1/27 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5/27 + a^4*c/9 + 16*a^3*b^2/27 - 8*a^3*c^2/27 - 8*a^2*b^3/27 - 4*a^2*b^2*c/9 - 4*a^2*b*c^2/9 + 16*a^2*c^3/27 + a*b^4/9 - 4*a*b^2*c^2/9 + b^5/27 + 16*b^3*c^2/27 - 8*b^2*c^3/27 + b*c^4/9 + c^5/27) := by
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
  have he : (a^3*b^2 + a^3 - a^2*b^2 + a^2*c^3 - a^2*c^2 + a^2*c - 2*a^2 + a*b^2 + a + b^3*c^2 + b^3 - b^2*c^2 - 2*b^2 + b*c^2 + b + c^3 - 2*c^2 + c - 3) = (a^5/27 + a^4*c/9 + 16*a^3*b^2/27 - 8*a^3*c^2/27 - 8*a^2*b^3/27 - 4*a^2*b^2*c/9 - 4*a^2*b*c^2/9 + 16*a^2*c^3/27 + a*b^4/9 - 4*a*b^2*c^2/9 + b^5/27 + 16*b^3*c^2/27 - 8*b^2*c^3/27 + b*c^4/9 + c^5/27) := by
    linear_combination (-a^4/27 + a^3*b/27 - 2*a^3*c/27 - a^3/9 + 10*a^2*b^2/27 + a^2*b*c/27 + 2*a^2*b/9 + 10*a^2*c^2/27 - a^2*c/9 + 2*a^2/3 - 2*a*b^3/27 + a*b^2*c/27 - a*b^2/9 + a*b*c^2/27 + a*c^3/27 + 2*a*c^2/9 - b^4/27 + b^3*c/27 - b^3/9 + 10*b^2*c^2/27 + 2*b^2*c/9 + 2*b^2/3 - 2*b*c^3/27 - b*c^2/9 - c^4/27 - c^3/9 + 2*c^2/3 + 1) * habc
  have hn : 0 ≤ (a^3*b^2 + a^3 - a^2*b^2 + a^2*c^3 - a^2*c^2 + a^2*c - 2*a^2 + a*b^2 + a + b^3*c^2 + b^3 - b^2*c^2 - 2*b^2 + b*c^2 + b + c^3 - 2*c^2 + c - 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + b)/(a^2 + 1) + (b^2 + c)/(b^2 + 1) + (c^2 + a)/(c^2 + 1) ≥ 3) := @solution
#print axioms solution
