-- Prove2me | solution 1 for WorkbookSource.plus_59647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:41:52.787643+00:00
-- url     : https://prove2.me/submissions/8f836df4-4832-4ee0-8c4b-665bbfbb84e9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^5 + b^5 + c^5 + a * b * c * (a * b + a * c + b * c) ≥ a^4 * b + b^4 * c + c^4 * a + a * b * c * (a^2 + b^2 + c^2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 - a^4*b - a^3*b*c + a^2*b^2*c + a^2*b*c^2 - a*b^3*c + a*b^2*c^2 - a*b*c^3 - a*c^4 + b^5 - b^4*c + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^3 * (b - a)^2 + (3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^3 * (c - b)^2 + (4 : ℝ) * a^2 * (b - a)^3 + (9 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^2 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^4 + (10 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (22 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^1 * (c - b)^4 + (1 : ℝ) * (b - a)^5 + (4 : ℝ) * (b - a)^4 * (c - b)^1 + (10 : ℝ) * (b - a)^3 * (c - b)^2 + (10 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5 - a^4*b - a^3*b*c + a^2*b^2*c + a^2*b*c^2 - a*b^3*c + a*b^2*c^2 - a*b*c^3 - a*c^4 + b^5 - b^4*c + c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^3 * (c - a)^2 + (3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^3 * (b - c)^2 + (4 : ℝ) * a^2 * (c - a)^3 + (3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (9 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^2 * (b - c)^3 + (3 : ℝ) * a^1 * (c - a)^4 + (2 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (10 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (11 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^1 * (b - c)^4 + (1 : ℝ) * (c - a)^5 + (1 : ℝ) * (c - a)^4 * (b - c)^1 + (4 : ℝ) * (c - a)^3 * (b - c)^2 + (6 : ℝ) * (c - a)^2 * (b - c)^3 + (4 : ℝ) * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 - a^4*b - a^3*b*c + a^2*b^2*c + a^2*b*c^2 - a*b^3*c + a*b^2*c^2 - a*b*c^3 - a*c^4 + b^5 - b^4*c + c^5) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), a^5 + b^5 + c^5 + a * b * c * (a * b + a * c + b * c) ≥ a^4 * b + b^4 * c + c^4 * a + a * b * c * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
