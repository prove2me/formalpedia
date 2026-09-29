-- Prove2me | solution 1 for WorkbookSource.base_27556
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:21.725681+00:00
-- url     : https://prove2.me/submissions/8a804ff3-2a6e-4cfb-b0a2-6de4d9c9dfb2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≤ 9 / (3 + b * c + c * a + a * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b/3 + 2*a^4*c/3 - 2*a^3*b^2/3 + 2*a^3*c^2/3 + 2*a^2*b^3/3 - a^2*b^2*c - a^2*b*c^2 - 2*a^2*c^3/3 + 2*a*b^4/3 - a*b^2*c^2 + a*c^4/3 + b^4*c/3 - 2*b^3*c^2/3 + 2*b^2*c^3/3 + 2*b*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (b - a)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^3 * (c - b)^2 + (8 : ℝ) * a^2 * (b - a)^3 + (15 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^2 * (c - b)^3 + (5 : ℝ) * a^1 * (b - a)^4 + (14 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (17 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (1 : ℝ) * (b - a)^5 + (11/3 : ℝ) * (b - a)^4 * (c - b)^1 + (16/3 : ℝ) * (b - a)^3 * (c - b)^2 + (10/3 : ℝ) * (b - a)^2 * (c - b)^3 + (2/3 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b/3 + 2*a^4*c/3 - 2*a^3*b^2/3 + 2*a^3*c^2/3 + 2*a^2*b^3/3 - a^2*b^2*c - a^2*b*c^2 - 2*a^2*c^3/3 + 2*a*b^4/3 - a*b^2*c^2 + a*c^4/3 + b^4*c/3 - 2*b^3*c^2/3 + 2*b^2*c^3/3 + 2*b*c^4/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (c - a)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^3 * (b - c)^2 + (8 : ℝ) * a^2 * (c - a)^3 + (9 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (9 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^2 * (b - c)^3 + (5 : ℝ) * a^1 * (c - a)^4 + (6 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (5 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (1 : ℝ) * (c - a)^5 + (4/3 : ℝ) * (c - a)^4 * (b - c)^1 + (2/3 : ℝ) * (c - a)^3 * (b - c)^2 + (2/3 : ℝ) * (c - a)^2 * (b - c)^3 + (1/3 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b/3 + 2*a^4*c/3 - 2*a^3*b^2/3 + 2*a^3*c^2/3 + 2*a^2*b^3/3 - a^2*b^2*c - a^2*b*c^2 - 2*a^2*c^3/3 + 2*a*b^4/3 - a*b^2*c^2 + a*c^4/3 + b^4*c/3 - 2*b^3*c^2/3 + 2*b^2*c^3/3 + 2*b*c^4/3) := by
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
  have he : (-2*a^3*b^2 - 3*a^3*b*c - a^3*c^2 - a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + 3*a^2*b - 2*a^2*c^3 + 6*a^2*c - 3*a*b^3*c - 6*a*b^2*c^2 + 6*a*b^2 - 3*a*b*c^3 + 9*a*b*c + 3*a*c^2 - 2*b^3*c^2 - b^2*c^3 + 3*b^2*c + 6*b*c^2) = (a^4*b/3 + 2*a^4*c/3 - 2*a^3*b^2/3 + 2*a^3*c^2/3 + 2*a^2*b^3/3 - a^2*b^2*c - a^2*b*c^2 - 2*a^2*c^3/3 + 2*a*b^4/3 - a*b^2*c^2 + a*c^4/3 + b^4*c/3 - 2*b^3*c^2/3 + 2*b^2*c^3/3 + 2*b*c^4/3) := by
    linear_combination (-a^3*b/3 - 2*a^3*c/3 - a^2*b^2 - 2*a^2*b*c - a^2*b - a^2*c^2 - 2*a^2*c - 2*a*b^3/3 - 2*a*b^2*c - 2*a*b^2 - 2*a*b*c^2 - 3*a*b*c - a*c^3/3 - a*c^2 - b^3*c/3 - b^2*c^2 - b^2*c - 2*b*c^3/3 - 2*b*c^2) * habc
  have hn : 0 ≤ (-2*a^3*b^2 - 3*a^3*b*c - a^3*c^2 - a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + 3*a^2*b - 2*a^2*c^3 + 6*a^2*c - 3*a*b^3*c - 6*a*b^2*c^2 + 6*a*b^2 - 3*a*b*c^3 + 9*a*b*c + 3*a*c^2 - 2*b^3*c^2 - b^2*c^3 + 3*b^2*c + 6*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (a + b) + b / (b + c) + c / (c + a) ≤ 9 / (3 + b * c + c * a + a * b)) := @solution
#print axioms solution
