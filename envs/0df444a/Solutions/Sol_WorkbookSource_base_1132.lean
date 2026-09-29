-- Prove2me | solution 1 for WorkbookSource.base_1132
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:26.987608+00:00
-- url     : https://prove2.me/submissions/ca5ce445-6786-49f2-8931-7ca4a98e8e0e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 / (3 * a * b * c) + (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 10  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 24*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 3*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 3*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 24*a*b^4*c + 3*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^4 * (b - a)^2 + (21 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^4 * (c - b)^2 + (63 : ℝ) * a^3 * (b - a)^3 + (96 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (75 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (21 : ℝ) * a^3 * (c - b)^3 + (90 : ℝ) * a^2 * (b - a)^4 + (183 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (180 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (87 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (27 : ℝ) * a^2 * (c - b)^4 + (63 : ℝ) * a^1 * (b - a)^5 + (159 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (195 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (132 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (57 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (72 : ℝ) * (b - a)^4 * (c - b)^2 + (64 : ℝ) * (b - a)^3 * (c - b)^3 + (33 : ℝ) * (b - a)^2 * (c - b)^4 + (9 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 24*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 3*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 3*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 24*a*b^4*c + 3*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^4 * (c - a)^2 + (21 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (21 : ℝ) * a^4 * (b - c)^2 + (63 : ℝ) * a^3 * (c - a)^3 + (93 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (72 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (21 : ℝ) * a^3 * (b - c)^3 + (90 : ℝ) * a^2 * (c - a)^4 + (177 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (171 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (84 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (27 : ℝ) * a^2 * (b - c)^4 + (63 : ℝ) * a^1 * (c - a)^5 + (156 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (189 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (129 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (57 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (12 : ℝ) * a^1 * (b - c)^5 + (16 : ℝ) * (c - a)^6 + (48 : ℝ) * (c - a)^5 * (b - c)^1 + (72 : ℝ) * (c - a)^4 * (b - c)^2 + (64 : ℝ) * (c - a)^3 * (b - c)^3 + (33 : ℝ) * (c - a)^2 * (b - c)^4 + (9 : ℝ) * (c - a)^1 * (b - c)^5 + (1 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 24*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 3*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 3*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 24*a*b^4*c + 3*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by
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
  have hn : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 24*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 3*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 3*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 24*a*b^4*c + 3*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 3 / (3 * a * b * c) + (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a ^ 3 + b ^ 3 + c ^ 3) ≥ 10) := @solution
#print axioms solution
