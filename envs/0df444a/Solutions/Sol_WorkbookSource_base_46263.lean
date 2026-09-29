-- Prove2me | solution 1 for WorkbookSource.base_46263
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:06:09.790848+00:00
-- url     : https://prove2.me/submissions/25610bab-38aa-4650-926d-ff5343df7578

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a * b * c + 12 / (a * b + b * c + c * a) ≥ 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5/81 + 5*a^4*b/81 + 5*a^4*c/81 - 5*a^3*b^2/81 - 25*a^3*b*c/81 - 5*a^3*c^2/81 - 5*a^2*b^3/81 + 7*a^2*b^2*c/27 + 7*a^2*b*c^2/27 - 5*a^2*c^3/81 + 5*a*b^4/81 - 25*a*b^3*c/81 + 7*a*b^2*c^2/27 - 25*a*b*c^3/81 + 5*a*c^4/81 + 4*b^5/81 + 5*b^4*c/81 - 5*b^3*c^2/81 - 5*b^2*c^3/81 + 5*b*c^4/81 + 4*c^5/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * a^3 * (b - a)^2 + (1/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1/3 : ℝ) * a^3 * (c - b)^2 + (4/9 : ℝ) * a^2 * (b - a)^3 + (2/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (4/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (5/9 : ℝ) * a^2 * (c - b)^3 + (7/27 : ℝ) * a^1 * (b - a)^4 + (14/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (14/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (35/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (10/27 : ℝ) * a^1 * (c - b)^4 + (8/81 : ℝ) * (b - a)^5 + (20/81 : ℝ) * (b - a)^4 * (c - b)^1 + (50/81 : ℝ) * (b - a)^3 * (c - b)^2 + (55/81 : ℝ) * (b - a)^2 * (c - b)^3 + (25/81 : ℝ) * (b - a)^1 * (c - b)^4 + (4/81 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5/81 + 5*a^4*b/81 + 5*a^4*c/81 - 5*a^3*b^2/81 - 25*a^3*b*c/81 - 5*a^3*c^2/81 - 5*a^2*b^3/81 + 7*a^2*b^2*c/27 + 7*a^2*b*c^2/27 - 5*a^2*c^3/81 + 5*a*b^4/81 - 25*a*b^3*c/81 + 7*a*b^2*c^2/27 - 25*a*b*c^3/81 + 5*a*c^4/81 + 4*b^5/81 + 5*b^4*c/81 - 5*b^3*c^2/81 - 5*b^2*c^3/81 + 5*b*c^4/81 + 4*c^5/81) := by
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
  have he : (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 5*a*b - 5*a*c - 5*b*c + 12) = (4*a^5/81 + 5*a^4*b/81 + 5*a^4*c/81 - 5*a^3*b^2/81 - 25*a^3*b*c/81 - 5*a^3*c^2/81 - 5*a^2*b^3/81 + 7*a^2*b^2*c/27 + 7*a^2*b*c^2/27 - 5*a^2*c^3/81 + 5*a*b^4/81 - 25*a*b^3*c/81 + 7*a*b^2*c^2/27 - 25*a*b*c^3/81 + 5*a*c^4/81 + 4*b^5/81 + 5*b^4*c/81 - 5*b^3*c^2/81 - 5*b^2*c^3/81 + 5*b*c^4/81 + 4*c^5/81) := by
    linear_combination (-4*a^4/81 - a^3*b/81 - a^3*c/81 - 4*a^3/27 + 2*a^2*b^2/27 + a^2*b*c/3 + a^2*b/9 + 2*a^2*c^2/27 + a^2*c/9 - 4*a^2/9 - a*b^3/81 + a*b^2*c/3 + a*b^2/9 + a*b*c^2/3 + 7*a*b*c/9 + 7*a*b/9 - a*c^3/81 + a*c^2/9 + 7*a*c/9 - 4*a/3 - 4*b^4/81 - b^3*c/81 - 4*b^3/27 + 2*b^2*c^2/27 + b^2*c/9 - 4*b^2/9 - b*c^3/81 + b*c^2/9 + 7*b*c/9 - 4*b/3 - 4*c^4/81 - 4*c^3/27 - 4*c^2/9 - 4*c/3 - 4) * habc
  have hn : 0 ≤ (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 5*a*b - 5*a*c - 5*b*c + 12) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a * b * c + 12 / (a * b + b * c + c * a) ≥ 5) := @solution
#print axioms solution
