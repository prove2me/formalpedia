-- Prove2me | solution 1 for WorkbookSource.base_855
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:21.901991+00:00
-- url     : https://prove2.me/submissions/a47e869b-8c84-48c1-b603-381b4088ee9b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (a + c) ^ 2) ≥ 9 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b + 4*a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 - 6*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 - 6*a^3*c^3 - a^2*b^4 - 2*a^2*b^3*c + 6*a^2*b^2*c^2 - 2*a^2*b*c^3 - a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 4*b^5*c - b^4*c^2 - 6*b^3*c^3 - b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^4 * (b - a)^2 + (32 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^4 * (c - b)^2 + (64 : ℝ) * a^3 * (b - a)^3 + (96 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (160 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^3 * (c - b)^3 + (40 : ℝ) * a^2 * (b - a)^4 + (80 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (216 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (176 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (40 : ℝ) * a^2 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^5 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (104 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (136 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (60 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^1 * (c - b)^5 + (15 : ℝ) * (b - a)^4 * (c - b)^2 + (30 : ℝ) * (b - a)^3 * (c - b)^3 + (19 : ℝ) * (b - a)^2 * (c - b)^4 + (4 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b + 4*a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 - 6*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 - 6*a^3*c^3 - a^2*b^4 - 2*a^2*b^3*c + 6*a^2*b^2*c^2 - 2*a^2*b*c^3 - a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 4*b^5*c - b^4*c^2 - 6*b^3*c^3 - b^2*c^4 + 4*b*c^5) := by
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
  have hn : 0 ≤ (4*a^5*b + 4*a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 - 6*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 - 6*a^3*c^3 - a^2*b^4 - 2*a^2*b^3*c + 6*a^2*b^2*c^2 - 2*a^2*b*c^3 - a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 4*b^5*c - b^4*c^2 - 6*b^3*c^3 - b^2*c^4 + 4*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (a + c) ^ 2) ≥ 9 / 4) := @solution
#print axioms solution
