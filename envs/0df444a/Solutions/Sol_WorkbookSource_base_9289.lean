-- Prove2me | solution 1 for WorkbookSource.base_9289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:17.46219+00:00
-- url     : https://prove2.me/submissions/a9a96008-44b4-4df6-bffc-e3adb6824a1f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (3 + a ^ 3 + b ^ 3 + c ^ 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (11*a^5*b/9 + a^5*c/9 - 2*a^4*b^2/9 + a^4*b*c/3 + 5*a^4*c^2/9 - a^3*b^3 + 2*a^3*b^2*c/9 - 8*a^3*b*c^2/9 - a^3*c^3 + 5*a^2*b^4/9 - 8*a^2*b^3*c/9 - a^2*b^2*c^2 + 2*a^2*b*c^3/9 - 2*a^2*c^4/9 + a*b^5/9 + a*b^4*c/3 + 2*a*b^3*c^2/9 - 8*a*b^2*c^3/9 + a*b*c^4/3 + 11*a*c^5/9 + 11*b^5*c/9 - 2*b^4*c^2/9 - b^3*c^3 + 5*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (56/3 : ℝ) * a^3 * (b - a)^3 + (25 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (33 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (40/3 : ℝ) * a^3 * (c - b)^3 + (46/3 : ℝ) * a^2 * (b - a)^4 + (74/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (41 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (95/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (22/3 : ℝ) * a^2 * (c - b)^4 + (16/3 : ℝ) * a^1 * (b - a)^5 + (25/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (50/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (59/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (26/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/3 : ℝ) * a^1 * (c - b)^5 + (2/3 : ℝ) * (b - a)^6 + (5/9 : ℝ) * (b - a)^5 * (c - b)^1 + (11/9 : ℝ) * (b - a)^4 * (c - b)^2 + (7/3 : ℝ) * (b - a)^3 * (c - b)^3 + (10/9 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (11*a^5*b/9 + a^5*c/9 - 2*a^4*b^2/9 + a^4*b*c/3 + 5*a^4*c^2/9 - a^3*b^3 + 2*a^3*b^2*c/9 - 8*a^3*b*c^2/9 - a^3*c^3 + 5*a^2*b^4/9 - 8*a^2*b^3*c/9 - a^2*b^2*c^2 + 2*a^2*b*c^3/9 - 2*a^2*c^4/9 + a*b^5/9 + a*b^4*c/3 + 2*a*b^3*c^2/9 - 8*a*b^2*c^3/9 + a*b*c^4/3 + 11*a*c^5/9 + 11*b^5*c/9 - 2*b^4*c^2/9 - b^3*c^3 + 5*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (c - a)^2 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^4 * (b - c)^2 + (56/3 : ℝ) * a^3 * (c - a)^3 + (31 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (39 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (40/3 : ℝ) * a^3 * (b - c)^3 + (46/3 : ℝ) * a^2 * (c - a)^4 + (110/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (59 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (113/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (22/3 : ℝ) * a^2 * (b - c)^4 + (16/3 : ℝ) * a^1 * (c - a)^5 + (55/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (110/3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (101/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (38/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/3 : ℝ) * a^1 * (b - c)^5 + (2/3 : ℝ) * (c - a)^6 + (31/9 : ℝ) * (c - a)^5 * (b - c)^1 + (76/9 : ℝ) * (c - a)^4 * (b - c)^2 + (31/3 : ℝ) * (c - a)^3 * (b - c)^3 + (53/9 : ℝ) * (c - a)^2 * (b - c)^4 + (11/9 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (11*a^5*b/9 + a^5*c/9 - 2*a^4*b^2/9 + a^4*b*c/3 + 5*a^4*c^2/9 - a^3*b^3 + 2*a^3*b^2*c/9 - 8*a^3*b*c^2/9 - a^3*c^3 + 5*a^2*b^4/9 - 8*a^2*b^3*c/9 - a^2*b^2*c^2 + 2*a^2*b*c^3/9 - 2*a^2*c^4/9 + a*b^5/9 + a*b^4*c/3 + 2*a*b^3*c^2/9 - 8*a*b^2*c^3/9 + a*b*c^4/3 + 11*a*c^5/9 + 11*b^5*c/9 - 2*b^4*c^2/9 - b^3*c^3 + 5*b^2*c^4/9 + b*c^5/9) := by
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
  have he : (2*a^5*b + a^5*c + a^4*b^2 + 3*a^4*b*c - 3*a^4*b + 2*a^4*c^2 - 3*a^4*c + 2*a^3*b^2*c - 3*a^3*b^2 + a^3*b*c^2 - 6*a^3*b*c - 3*a^3*c^2 + 2*a^2*b^4 + a^2*b^3*c - 3*a^2*b^3 - 6*a^2*b^2*c + 2*a^2*b*c^3 - 6*a^2*b*c^2 + 6*a^2*b + a^2*c^4 - 3*a^2*c^3 + 3*a^2*c + a*b^5 + 3*a*b^4*c - 3*a*b^4 + 2*a*b^3*c^2 - 6*a*b^3*c + a*b^2*c^3 - 6*a*b^2*c^2 + 3*a*b^2 + 3*a*b*c^4 - 6*a*b*c^3 + 9*a*b*c + 2*a*c^5 - 3*a*c^4 + 6*a*c^2 + 2*b^5*c + b^4*c^2 - 3*b^4*c - 3*b^3*c^2 + 2*b^2*c^4 - 3*b^2*c^3 + 6*b^2*c + b*c^5 - 3*b*c^4 + 3*b*c^2) = (11*a^5*b/9 + a^5*c/9 - 2*a^4*b^2/9 + a^4*b*c/3 + 5*a^4*c^2/9 - a^3*b^3 + 2*a^3*b^2*c/9 - 8*a^3*b*c^2/9 - a^3*c^3 + 5*a^2*b^4/9 - 8*a^2*b^3*c/9 - a^2*b^2*c^2 + 2*a^2*b*c^3/9 - 2*a^2*c^4/9 + a*b^5/9 + a*b^4*c/3 + 2*a*b^3*c^2/9 - 8*a*b^2*c^3/9 + a*b*c^4/3 + 11*a*c^5/9 + 11*b^5*c/9 - 2*b^4*c^2/9 - b^3*c^3 + 5*b^2*c^4/9 + b*c^5/9) := by
    linear_combination (7*a^4*b/9 + 8*a^4*c/9 + 4*a^3*b^2/9 + a^3*b*c - 2*a^3*b/3 + 5*a^3*c^2/9 - a^3*c/3 + 5*a^2*b^3/9 + a^2*b^2*c/3 - a^2*b^2 + a^2*b*c^2/3 - 2*a^2*b*c - 2*a^2*b + 4*a^2*c^3/9 - a^2*c^2 - a^2*c + 8*a*b^4/9 + a*b^3*c - a*b^3/3 + a*b^2*c^2/3 - 2*a*b^2*c - a*b^2 + a*b*c^3 - 2*a*b*c^2 - 3*a*b*c + 7*a*c^4/9 - 2*a*c^3/3 - 2*a*c^2 + 7*b^4*c/9 + 4*b^3*c^2/9 - 2*b^3*c/3 + 5*b^2*c^3/9 - b^2*c^2 - 2*b^2*c + 8*b*c^4/9 - b*c^3/3 - b*c^2) * hab
  have hn : 0 ≤ (2*a^5*b + a^5*c + a^4*b^2 + 3*a^4*b*c - 3*a^4*b + 2*a^4*c^2 - 3*a^4*c + 2*a^3*b^2*c - 3*a^3*b^2 + a^3*b*c^2 - 6*a^3*b*c - 3*a^3*c^2 + 2*a^2*b^4 + a^2*b^3*c - 3*a^2*b^3 - 6*a^2*b^2*c + 2*a^2*b*c^3 - 6*a^2*b*c^2 + 6*a^2*b + a^2*c^4 - 3*a^2*c^3 + 3*a^2*c + a*b^5 + 3*a*b^4*c - 3*a*b^4 + 2*a*b^3*c^2 - 6*a*b^3*c + a*b^2*c^3 - 6*a*b^2*c^2 + 3*a*b^2 + 3*a*b*c^4 - 6*a*b*c^3 + 9*a*b*c + 2*a*c^5 - 3*a*c^4 + 6*a*c^2 + 2*b^5*c + b^4*c^2 - 3*b^4*c - 3*b^3*c^2 + 2*b^2*c^4 - 3*b^2*c^3 + 6*b^2*c + b*c^5 - 3*b*c^4 + 3*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a + b) + b / (b + c) + c / (c + a) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (3 + a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
