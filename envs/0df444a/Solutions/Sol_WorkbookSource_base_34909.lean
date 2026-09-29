-- Prove2me | solution 1 for WorkbookSource.base_34909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:20.65471+00:00
-- url     : https://prove2.me/submissions/6bbe1af9-cd38-4a40-bf66-b9eae43c4a8f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 1) + (c + a) / (b + 1) + (a + b) / (c + 1) ≥ 6 * (a + b + c) / (a + b + c + 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3*b + a^3*c + 2*a^3 + 2*a^2*b^2 - 4*a^2*b*c + a^2*b + 2*a^2*c^2 + a^2*c + 2*a^2 + a*b^3 - 4*a*b^2*c + a*b^2 - 4*a*b*c^2 - 12*a*b*c - 2*a*b + a*c^3 + a*c^2 - 2*a*c + b^3*c + 2*b^3 + 2*b^2*c^2 + b^2*c + 2*b^2 + b*c^3 + b*c^2 - 2*b*c + 2*c^3 + 2*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^2 * (b - a)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^2 * (c - b)^2 + (10 : ℝ) * a^1 * (b - a)^3 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (8 : ℝ) * a^1 * (b - a)^2 + (9 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^1 * (c - b)^3 + (8 : ℝ) * a^1 * (c - b)^2 + (4 : ℝ) * (b - a)^4 + (8 : ℝ) * (b - a)^3 * (c - b)^1 + (6 : ℝ) * (b - a)^3 + (5 : ℝ) * (b - a)^2 * (c - b)^2 + (9 : ℝ) * (b - a)^2 * (c - b)^1 + (2 : ℝ) * (b - a)^2 + (1 : ℝ) * (b - a)^1 * (c - b)^3 + (7 : ℝ) * (b - a)^1 * (c - b)^2 + (2 : ℝ) * (b - a)^1 * (c - b)^1 + (2 : ℝ) * (c - b)^3 + (2 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b + a^3*c + 2*a^3 + 2*a^2*b^2 - 4*a^2*b*c + a^2*b + 2*a^2*c^2 + a^2*c + 2*a^2 + a*b^3 - 4*a*b^2*c + a*b^2 - 4*a*b*c^2 - 12*a*b*c - 2*a*b + a*c^3 + a*c^2 - 2*a*c + b^3*c + 2*b^3 + 2*b^2*c^2 + b^2*c + 2*b^2 + b*c^3 + b*c^2 - 2*b*c + 2*c^3 + 2*c^2) := by
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
  have hn : 0 ≤ ((a + b + c + 1)*(a^2*b + a^2*c + 2*a^2 + a*b^2 - 6*a*b*c - 2*a*b + a*c^2 - 2*a*c + b^2*c + 2*b^2 + b*c^2 - 2*b*c + 2*c^2)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b + c) / (a + 1) + (c + a) / (b + 1) + (a + b) / (c + 1) ≥ 6 * (a + b + c) / (a + b + c + 3)) := @solution
#print axioms solution
