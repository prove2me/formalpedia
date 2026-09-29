-- Prove2me | solution 1 for WorkbookSource.base_28197
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:19.445214+00:00
-- url     : https://prove2.me/submissions/9fd63a4b-c20d-4225-9813-4709d281f13f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + 2 * b * c) / (b + c) ^ 2 + (b^2 + 2 * c * a) / (c + a) ^ 2 + (c^2 + 2 * a * b) / (a + b) ^ 2 ≥ 9 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 8*a^5*b + 8*a^5*c - 5*a^4*b^2 + 6*a^4*b*c - 5*a^4*c^2 - 10*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 10*a^3*c^3 - 5*a^2*b^4 - 6*a^2*b^3*c + 18*a^2*b^2*c^2 - 6*a^2*b*c^3 - 5*a^2*c^4 + 8*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 8*a*c^5 + 4*b^6 + 8*b^5*c - 5*b^4*c^2 - 10*b^3*c^3 - 5*b^2*c^4 + 8*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^4 * (b - a)^2 + (96 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^4 * (c - b)^2 + (192 : ℝ) * a^3 * (b - a)^3 + (288 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (480 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (192 : ℝ) * a^3 * (c - b)^3 + (136 : ℝ) * a^2 * (b - a)^4 + (272 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (696 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (560 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (136 : ℝ) * a^2 * (c - b)^4 + (40 : ℝ) * a^1 * (b - a)^5 + (100 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (392 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (488 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (236 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (40 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (75 : ℝ) * (b - a)^4 * (c - b)^2 + (130 : ℝ) * (b - a)^3 * (c - b)^3 + (95 : ℝ) * (b - a)^2 * (c - b)^4 + (32 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 8*a^5*b + 8*a^5*c - 5*a^4*b^2 + 6*a^4*b*c - 5*a^4*c^2 - 10*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 10*a^3*c^3 - 5*a^2*b^4 - 6*a^2*b^3*c + 18*a^2*b^2*c^2 - 6*a^2*b*c^3 - 5*a^2*c^4 + 8*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 8*a*c^5 + 4*b^6 + 8*b^5*c - 5*b^4*c^2 - 10*b^3*c^3 - 5*b^2*c^4 + 8*b*c^5 + 4*c^6) := by
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
  have hn : 0 ≤ (4*a^6 + 8*a^5*b + 8*a^5*c - 5*a^4*b^2 + 6*a^4*b*c - 5*a^4*c^2 - 10*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 10*a^3*c^3 - 5*a^2*b^4 - 6*a^2*b^3*c + 18*a^2*b^2*c^2 - 6*a^2*b*c^3 - 5*a^2*c^4 + 8*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 8*a*c^5 + 4*b^6 + 8*b^5*c - 5*b^4*c^2 - 10*b^3*c^3 - 5*b^2*c^4 + 8*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^2 + 2 * b * c) / (b + c) ^ 2 + (b^2 + 2 * c * a) / (c + a) ^ 2 + (c^2 + 2 * a * b) / (a + b) ^ 2 ≥ 9 / 4) := @solution
#print axioms solution
