-- Prove2me | solution 1 for WorkbookSource.plus_1587
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:40.083329+00:00
-- url     : https://prove2.me/submissions/28395137-af44-4c53-a029-bea7b89982a9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (27 * a * b * c) / (a + b + c) ^ 3 + 2 ≥ (3 * (a * b + b * c + a * c)) / (a ^ 2 + b ^ 2 + c ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + 3*a^4*b + 3*a^4*c - a^3*b^2 + 18*a^3*b*c - a^3*c^2 - a^2*b^3 - 24*a^2*b^2*c - 24*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 + 18*a*b^3*c - 24*a*b^2*c^2 + 18*a*b*c^3 + 3*a*c^4 + 2*b^5 + 3*b^4*c - b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (54 : ℝ) * a^3 * (b - a)^2 + (54 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (54 : ℝ) * a^3 * (c - b)^2 + (102 : ℝ) * a^2 * (b - a)^3 + (153 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (171 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (60 : ℝ) * a^2 * (c - b)^3 + (58 : ℝ) * a^1 * (b - a)^4 + (116 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (150 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (92 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^1 * (c - b)^4 + (8 : ℝ) * (b - a)^5 + (20 : ℝ) * (b - a)^4 * (c - b)^1 + (34 : ℝ) * (b - a)^3 * (c - b)^2 + (31 : ℝ) * (b - a)^2 * (c - b)^3 + (13 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 3*a^4*b + 3*a^4*c - a^3*b^2 + 18*a^3*b*c - a^3*c^2 - a^2*b^3 - 24*a^2*b^2*c - 24*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 + 18*a*b^3*c - 24*a*b^2*c^2 + 18*a*b*c^3 + 3*a*c^4 + 2*b^5 + 3*b^4*c - b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 + 3*a^4*b + 3*a^4*c - a^3*b^2 + 18*a^3*b*c - a^3*c^2 - a^2*b^3 - 24*a^2*b^2*c - 24*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 + 18*a*b^3*c - 24*a*b^2*c^2 + 18*a*b*c^3 + 3*a*c^4 + 2*b^5 + 3*b^4*c - b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (27 * a * b * c) / (a + b + c) ^ 3 + 2 ≥ (3 * (a * b + b * c + a * c)) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
