-- Prove2me | solution 1 for WorkbookSource.base_27353
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:38.96172+00:00
-- url     : https://prove2.me/submissions/7f692f6f-7bf7-4e8d-abe3-0b66563c8768

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*c + 2*a^3*b*c + a^3*c^2 + a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 2*a*b^4 + 2*a*b^3*c - 5*a*b^2*c^2 + 2*a*b*c^3 + b^2*c^3 + 2*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (b - a)^2 + (12 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^3 * (c - b)^2 + (25 : ℝ) * a^2 * (b - a)^3 + (45 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (42 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (11 : ℝ) * a^2 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^4 + (42 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (46 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^1 * (c - b)^4 + (3 : ℝ) * (b - a)^5 + (11 : ℝ) * (b - a)^4 * (c - b)^1 + (15 : ℝ) * (b - a)^3 * (c - b)^2 + (9 : ℝ) * (b - a)^2 * (c - b)^3 + (2 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*c + 2*a^3*b*c + a^3*c^2 + a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 2*a*b^4 + 2*a*b^3*c - 5*a*b^2*c^2 + 2*a*b*c^3 + b^2*c^3 + 2*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (c - a)^2 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^3 * (b - c)^2 + (25 : ℝ) * a^2 * (c - a)^3 + (30 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (27 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (11 : ℝ) * a^2 * (b - c)^3 + (16 : ℝ) * a^1 * (c - a)^4 + (22 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (16 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (10 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^1 * (b - c)^4 + (3 : ℝ) * (c - a)^5 + (4 : ℝ) * (c - a)^4 * (b - c)^1 + (1 : ℝ) * (c - a)^3 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*c + 2*a^3*b*c + a^3*c^2 + a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 2*a*b^4 + 2*a*b^3*c - 5*a*b^2*c^2 + 2*a*b*c^3 + b^2*c^3 + 2*b*c^4) := by
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
  have hn : 0 ≤ (2*a^4*c + 2*a^3*b*c + a^3*c^2 + a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 2*a*b^4 + 2*a*b^3*c - 5*a*b^2*c^2 + 2*a*b*c^3 + b^2*c^3 + 2*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) := @solution
#print axioms solution
