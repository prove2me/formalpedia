-- Prove2me | solution 1 for WorkbookSource.plus_45883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:58.886848+00:00
-- url     : https://prove2.me/submissions/871a634d-bb26-4987-a0e0-83caf64424e0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ((c + a) / b + 2 * c / (a + b)) * ((a + b) / c + 2 * a / (b + c)) * ((b + c) / a + 2 * b / (c + a)) ≥ 27   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^4*b^2 + 10*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 9*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 9*a^2*b^3*c - 12*a^2*b^2*c^2 - 9*a^2*b*c^3 + 3*a^2*c^4 + 10*a*b^4*c - 9*a*b^3*c^2 - 9*a*b^2*c^3 + 10*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (54 : ℝ) * a^4 * (b - a)^2 + (54 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (54 : ℝ) * a^4 * (c - b)^2 + (158 : ℝ) * a^3 * (b - a)^3 + (237 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (195 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (58 : ℝ) * a^3 * (c - b)^3 + (166 : ℝ) * a^2 * (b - a)^4 + (332 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (285 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (119 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^2 * (c - b)^4 + (74 : ℝ) * a^1 * (b - a)^5 + (185 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (180 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (85 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (39 : ℝ) * (b - a)^4 * (c - b)^2 + (18 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4*b^2 + 10*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 9*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 9*a^2*b^3*c - 12*a^2*b^2*c^2 - 9*a^2*b*c^3 + 3*a^2*c^4 + 10*a*b^4*c - 9*a*b^3*c^2 - 9*a*b^2*c^3 + 10*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by
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
  have hn : 0 ≤ (3*a^4*b^2 + 10*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 9*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 9*a^2*b^3*c - 12*a^2*b^2*c^2 - 9*a^2*b*c^3 + 3*a^2*c^4 + 10*a*b^4*c - 9*a*b^3*c^2 - 9*a*b^2*c^3 + 10*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), ((c + a) / b + 2 * c / (a + b)) * ((a + b) / c + 2 * a / (b + c)) * ((b + c) / a + 2 * b / (c + a)) ≥ 27) := @solution
#print axioms solution
