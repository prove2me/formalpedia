-- Prove2me | solution 1 for WorkbookSource.base_44125
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:26.69158+00:00
-- url     : https://prove2.me/submissions/bd7836df-d4b4-42c3-b767-3ca79ebda4f6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ a^2 + b^2 + c^2 + 9 / 16  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (17*a^4/9 + 4*a^3*b + 4*a^3*c - 106*a^2*b^2/9 + 44*a^2*b*c/9 - 106*a^2*c^2/9 + 4*a*b^3 + 44*a*b^2*c/9 + 44*a*b*c^2/9 + 4*a*c^3 + 17*b^4/9 + 4*b^3*c - 106*b^2*c^2/9 + 4*b*c^3 + 17*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 + (24 : ℝ) * a^3 * (b - a)^1 + (12 : ℝ) * a^3 * (c - b)^1 + (104/3 : ℝ) * a^2 * (b - a)^2 + (104/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (50/3 : ℝ) * a^2 * (c - b)^2 + (160/9 : ℝ) * a^1 * (b - a)^3 + (80/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (140/9 : ℝ) * a^1 * (c - b)^3 + (104/9 : ℝ) * (b - a)^2 * (c - b)^2 + (104/9 : ℝ) * (b - a)^1 * (c - b)^3 + (17/9 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (17*a^4/9 + 4*a^3*b + 4*a^3*c - 106*a^2*b^2/9 + 44*a^2*b*c/9 - 106*a^2*c^2/9 + 4*a*b^3 + 44*a*b^2*c/9 + 44*a*b*c^2/9 + 4*a*c^3 + 17*b^4/9 + 4*b^3*c - 106*b^2*c^2/9 + 4*b*c^3 + 17*c^4/9) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-16*a^2*b^2 - 16*a^2*c^2 + 16*a^2 - 16*b^2*c^2 + 16*b^2 + 16*c^2 + 9) = (17*a^4/9 + 4*a^3*b + 4*a^3*c - 106*a^2*b^2/9 + 44*a^2*b*c/9 - 106*a^2*c^2/9 + 4*a*b^3 + 44*a*b^2*c/9 + 44*a*b*c^2/9 + 4*a*c^3 + 17*b^4/9 + 4*b^3*c - 106*b^2*c^2/9 + 4*b*c^3 + 17*c^4/9) := by
    linear_combination (-17*a^3/9 - 19*a^2*b/9 - 19*a^2*c/9 - 17*a^2/3 - 19*a*b^2/9 - 2*a*b*c/3 - 2*a*b/3 - 19*a*c^2/9 - 2*a*c/3 - a - 17*b^3/9 - 19*b^2*c/9 - 17*b^2/3 - 19*b*c^2/9 - 2*b*c/3 - b - 17*c^3/9 - 17*c^2/3 - c - 3) * habc
  have hn : 0 ≤ (-16*a^2*b^2 - 16*a^2*c^2 + 16*a^2 - 16*b^2*c^2 + 16*b^2 + 16*c^2 + 9) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ a^2 + b^2 + c^2 + 9 / 16) := @solution
#print axioms solution
