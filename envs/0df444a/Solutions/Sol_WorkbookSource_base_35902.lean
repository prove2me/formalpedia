-- Prove2me | solution 1 for WorkbookSource.base_35902
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:27.700371+00:00
-- url     : https://prove2.me/submissions/b6b41c95-30c7-4a7a-82f9-69ff865d0eaa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c / (a + b) + b / (a + c) + a / (b + c)) ≤ (3 / 2) * (a / b + b / c + c / a - 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^4 * (b - a)^2 + (20 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^4 * (c - b)^2 + (62 : ℝ) * a^3 * (b - a)^3 + (105 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (79 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^3 * (c - b)^3 + (70 : ℝ) * a^2 * (b - a)^4 + (164 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (141 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (47 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (34 : ℝ) * a^1 * (b - a)^5 + (100 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (106 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (47 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (b - a)^6 + (21 : ℝ) * (b - a)^5 * (c - b)^1 + (27 : ℝ) * (b - a)^4 * (c - b)^2 + (15 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^4 * (c - a)^2 + (20 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (20 : ℝ) * a^4 * (b - c)^2 + (62 : ℝ) * a^3 * (c - a)^3 + (81 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (55 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (18 : ℝ) * a^3 * (b - c)^3 + (70 : ℝ) * a^2 * (c - a)^4 + (116 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (69 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (23 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (34 : ℝ) * a^1 * (c - a)^5 + (70 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (46 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (11 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * (c - a)^6 + (15 : ℝ) * (c - a)^5 * (b - c)^1 + (12 : ℝ) * (c - a)^4 * (b - c)^2 + (3 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b*c + 3*a^4*c^2 + 3*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 + 3*a^2*b^4 - 2*a^2*b^3*c - 9*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 3*b^3*c^3 + 3*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (c / (a + b) + b / (a + c) + a / (b + c)) ≤ (3 / 2) * (a / b + b / c + c / a - 2)) := @solution
#print axioms solution
