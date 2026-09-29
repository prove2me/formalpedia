-- Prove2me | solution 1 for WorkbookSource.base_42774
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:43.131927+00:00
-- url     : https://prove2.me/submissions/d065fa68-ce70-475e-a37c-2e8a5cc4e0c4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c) + (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b + 4*a^4*c - a^3*b^2 + 12*a^3*b*c - a^3*c^2 - a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 - a^2*c^3 + 4*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 4*a*c^4 + 4*b^4*c - b^3*c^2 - b^2*c^3 + 4*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^3 * (b - a)^2 + (40 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^3 * (c - b)^2 + (78 : ℝ) * a^2 * (b - a)^3 + (117 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (123 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^2 * (c - b)^3 + (44 : ℝ) * a^1 * (b - a)^4 + (88 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (102 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (58 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^5 + (15 : ℝ) * (b - a)^4 * (c - b)^1 + (20 : ℝ) * (b - a)^3 * (c - b)^2 + (15 : ℝ) * (b - a)^2 * (c - b)^3 + (4 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b + 4*a^4*c - a^3*b^2 + 12*a^3*b*c - a^3*c^2 - a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 - a^2*c^3 + 4*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 4*a*c^4 + 4*b^4*c - b^3*c^2 - b^2*c^3 + 4*b*c^4) := by
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
  have hn : 0 ≤ (4*a^4*b + 4*a^4*c - a^3*b^2 + 12*a^3*b*c - a^3*c^2 - a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 - a^2*c^3 + 4*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 4*a*c^4 + 4*b^4*c - b^3*c^2 - b^2*c^3 + 4*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c) + (a * b + b * c + c * a) / (2 * (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 2) := @solution
#print axioms solution
