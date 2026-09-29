-- Prove2me | solution 1 for WorkbookSource.base_32038
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:02.498386+00:00
-- url     : https://prove2.me/submissions/d6c4960c-c31a-4cb1-9a97-f71191db8d0e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a + 5 * b + 2 * c) + b / (5 * b + 5 * c + 2 * a) + c / (5 * c + 5 * a + 2 * b)) ≤ 1 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^3 - 21*a^2*b + 15*a^2*c + 15*a*b^2 - 12*a*b*c - 21*a*c^2 + 10*b^3 - 21*b^2*c + 15*b*c^2 + 10*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^1 * (b - a)^2 + (24 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^1 * (c - b)^2 + (14 : ℝ) * (b - a)^3 + (39 : ℝ) * (b - a)^2 * (c - b)^1 + (45 : ℝ) * (b - a)^1 * (c - b)^2 + (10 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^3 - 21*a^2*b + 15*a^2*c + 15*a*b^2 - 12*a*b*c - 21*a*c^2 + 10*b^3 - 21*b^2*c + 15*b*c^2 + 10*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^1 * (c - a)^2 + (24 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^1 * (b - c)^2 + (14 : ℝ) * (c - a)^3 + (3 : ℝ) * (c - a)^2 * (b - c)^1 + (9 : ℝ) * (c - a)^1 * (b - c)^2 + (10 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^3 - 21*a^2*b + 15*a^2*c + 15*a*b^2 - 12*a*b*c - 21*a*c^2 + 10*b^3 - 21*b^2*c + 15*b*c^2 + 10*c^3) := by
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
  have hn : 0 ≤ (10*a^3 - 21*a^2*b + 15*a^2*c + 15*a*b^2 - 12*a*b*c - 21*a*c^2 + 10*b^3 - 21*b^2*c + 15*b*c^2 + 10*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (5 * a + 5 * b + 2 * c) + b / (5 * b + 5 * c + 2 * a) + c / (5 * c + 5 * a + 2 * b)) ≤ 1 / 4) := @solution
#print axioms solution
