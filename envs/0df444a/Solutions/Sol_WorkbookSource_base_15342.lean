-- Prove2me | solution 1 for WorkbookSource.base_15342
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:04.586048+00:00
-- url     : https://prove2.me/submissions/05894b1a-10d7-432f-b8a7-ae9fece174f6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 4 + 15 * a * b * c + (a - b) * (b - c) * (c - a) ≥ 5 * (a^2 * b + b^2 * c + c^2 * a) + 12 * (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^3 - 6*a^2*b + a^2*c + a*b^2 + 3*a*b*c - 6*a*c^2 + 4*b^3 - 6*b^2*c + b*c^2 + 4*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^1 * (b - a)^2 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (7 : ℝ) * a^1 * (c - b)^2 + (3 : ℝ) * (b - a)^3 + (8 : ℝ) * (b - a)^2 * (c - b)^1 + (13 : ℝ) * (b - a)^1 * (c - b)^2 + (4 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^3 - 6*a^2*b + a^2*c + a*b^2 + 3*a*b*c - 6*a*c^2 + 4*b^3 - 6*b^2*c + b*c^2 + 4*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^1 * (c - a)^2 + (7 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (7 : ℝ) * a^1 * (b - c)^2 + (3 : ℝ) * (c - a)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^1 + (6 : ℝ) * (c - a)^1 * (b - c)^2 + (4 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^3 - 6*a^2*b + a^2*c + a*b^2 + 3*a*b*c - 6*a*c^2 + 4*b^3 - 6*b^2*c + b*c^2 + 4*c^3) := by
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
  have he : (-6*a^2*b + a^2*c + a*b^2 + 15*a*b*c - 12*a*b - 6*a*c^2 - 12*a*c - 6*b^2*c + b*c^2 - 12*b*c + 4) = (4*a^3 - 6*a^2*b + a^2*c + a*b^2 + 3*a*b*c - 6*a*c^2 + 4*b^3 - 6*b^2*c + b*c^2 + 4*c^3) := by
    linear_combination (-4*a^2 + 4*a*b + 4*a*c - 4*a - 4*b^2 + 4*b*c - 4*b - 4*c^2 - 4*c - 4) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1), 4 + 15 * a * b * c + (a - b) * (b - c) * (c - a) ≥ 5 * (a^2 * b + b^2 * c + c^2 * a) + 12 * (a * b + b * c + c * a)) := @solution
#print axioms solution
