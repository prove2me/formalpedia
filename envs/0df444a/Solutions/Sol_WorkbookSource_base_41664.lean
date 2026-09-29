-- Prove2me | solution 1 for WorkbookSource.base_41664
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:48.014626+00:00
-- url     : https://prove2.me/submissions/d3f6c321-6f95-4c61-98ab-b281ccfd206d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / a ^ 2 + c / b ^ 2 + a / c ^ 2) ≥ 9 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + a^3*b^3 + a^3*b^2*c + a^3*c^3 - 9*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^3*c^2 + b^4*c^2 + b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (25 : ℝ) * a^3 * (b - a)^3 + (33 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (22 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (7 : ℝ) * a^3 * (c - b)^3 + (28 : ℝ) * a^2 * (b - a)^4 + (47 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (8 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^2 * (c - b)^4 + (13 : ℝ) * a^1 * (b - a)^5 + (27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (17 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * (b - a)^6 + (5 : ℝ) * (b - a)^5 * (c - b)^1 + (4 : ℝ) * (b - a)^4 * (c - b)^2 + (1 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b^2 + a^3*b^3 + a^3*b^2*c + a^3*c^3 - 9*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^3*c^2 + b^4*c^2 + b^3*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (c - a)^2 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^4 * (b - c)^2 + (25 : ℝ) * a^3 * (c - a)^3 + (42 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (31 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (7 : ℝ) * a^3 * (b - c)^3 + (28 : ℝ) * a^2 * (c - a)^4 + (65 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (54 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (17 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^2 * (b - c)^4 + (13 : ℝ) * a^1 * (c - a)^5 + (38 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (39 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (16 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (c - a)^6 + (7 : ℝ) * (c - a)^5 * (b - c)^1 + (9 : ℝ) * (c - a)^4 * (b - c)^2 + (5 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + a^3*b^3 + a^3*b^2*c + a^3*c^3 - 9*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^3*c^2 + b^4*c^2 + b^3*c^3) := by
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
  have hn : 0 ≤ (a^4*b^2 + a^3*b^3 + a^3*b^2*c + a^3*c^3 - 9*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^3*c^2 + b^4*c^2 + b^3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b / a ^ 2 + c / b ^ 2 + a / c ^ 2) ≥ 9 / (a + b + c)) := @solution
#print axioms solution
