-- Prove2me | solution 1 for WorkbookSource.base_52341
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:24.227683+00:00
-- url     : https://prove2.me/submissions/59eaa250-4464-4a3c-8fc9-97397f82cdc7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2 + 4 * c^2) / b / c + (b^2 + 2 * c^2 + 4 * a^2) / c / a + (c^2 + 2 * a^2 + 4 * b^2) / a / b ≥ 21  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3 + 4*a^2*b + 2*a^2*c + 2*a*b^2 - 21*a*b*c + 4*a*c^2 + b^3 + 4*b^2*c + 2*b*c^2 + c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^1 * (b - a)^2 + (9 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^1 * (c - b)^2 + (8 : ℝ) * (b - a)^3 + (11 : ℝ) * (b - a)^2 * (c - b)^1 + (5 : ℝ) * (b - a)^1 * (c - b)^2 + (1 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^3 + 4*a^2*b + 2*a^2*c + 2*a*b^2 - 21*a*b*c + 4*a*c^2 + b^3 + 4*b^2*c + 2*b*c^2 + c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^1 * (c - a)^2 + (9 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (9 : ℝ) * a^1 * (b - c)^2 + (8 : ℝ) * (c - a)^3 + (13 : ℝ) * (c - a)^2 * (b - c)^1 + (7 : ℝ) * (c - a)^1 * (b - c)^2 + (1 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3 + 4*a^2*b + 2*a^2*c + 2*a*b^2 - 21*a*b*c + 4*a*c^2 + b^3 + 4*b^2*c + 2*b*c^2 + c^3) := by
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
  have hn : 0 ≤ (a^3 + 4*a^2*b + 2*a^2*c + 2*a*b^2 - 21*a*b*c + 4*a*c^2 + b^3 + 4*b^2*c + 2*b*c^2 + c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 2 * b^2 + 4 * c^2) / b / c + (b^2 + 2 * c^2 + 4 * a^2) / c / a + (c^2 + 2 * a^2 + 4 * b^2) / a / b ≥ 21) := @solution
#print axioms solution
