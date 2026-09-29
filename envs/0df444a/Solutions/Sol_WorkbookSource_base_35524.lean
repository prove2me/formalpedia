-- Prove2me | solution 1 for WorkbookSource.base_35524
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:53.243055+00:00
-- url     : https://prove2.me/submissions/a33c0d72-c9c9-47e5-b41e-52d9ecb4262f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b / (a ^ 2 + 2 * b ^ 2) + b * c / (b ^ 2 + 2 * c ^ 2) + c * a / (c ^ 2 + 2 * a ^ 2) ≤ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b^2 - 2*a^4*b*c + 4*a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - 4*a^3*b*c^2 - 2*a^3*c^3 + 4*a^2*b^4 - 4*a^2*b^3*c + 9*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - 2*a*b^4*c - a*b^3*c^2 - 4*a*b^2*c^3 - 2*a*b*c^4 + 2*b^4*c^2 - 2*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^4 * (b - a)^2 + (7 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (7 : ℝ) * a^4 * (c - b)^2 + (21 : ℝ) * a^3 * (b - a)^3 + (38 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (31 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (7 : ℝ) * a^3 * (c - b)^3 + (25 : ℝ) * a^2 * (b - a)^4 + (63 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (25 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (15 : ℝ) * a^1 * (b - a)^5 + (46 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (55 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (14 : ℝ) * (b - a)^5 * (c - b)^1 + (20 : ℝ) * (b - a)^4 * (c - b)^2 + (14 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b^2 - 2*a^4*b*c + 4*a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - 4*a^3*b*c^2 - 2*a^3*c^3 + 4*a^2*b^4 - 4*a^2*b^3*c + 9*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - 2*a*b^4*c - a*b^3*c^2 - 4*a*b^2*c^3 - 2*a*b*c^4 + 2*b^4*c^2 - 2*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^4 * (c - a)^2 + (7 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (7 : ℝ) * a^4 * (b - c)^2 + (21 : ℝ) * a^3 * (c - a)^3 + (25 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (18 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (7 : ℝ) * a^3 * (b - c)^3 + (25 : ℝ) * a^2 * (c - a)^4 + (37 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (24 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (12 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (15 : ℝ) * a^1 * (c - a)^5 + (29 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (21 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (10 : ℝ) * (c - a)^5 * (b - c)^1 + (10 : ℝ) * (c - a)^4 * (b - c)^2 + (6 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^2 - 2*a^4*b*c + 4*a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - 4*a^3*b*c^2 - 2*a^3*c^3 + 4*a^2*b^4 - 4*a^2*b^3*c + 9*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - 2*a*b^4*c - a*b^3*c^2 - 4*a*b^2*c^3 - 2*a*b*c^4 + 2*b^4*c^2 - 2*b^3*c^3 + 4*b^2*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b^2 - 2*a^4*b*c + 4*a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - 4*a^3*b*c^2 - 2*a^3*c^3 + 4*a^2*b^4 - 4*a^2*b^3*c + 9*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 - 2*a*b^4*c - a*b^3*c^2 - 4*a*b^2*c^3 - 2*a*b*c^4 + 2*b^4*c^2 - 2*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b / (a ^ 2 + 2 * b ^ 2) + b * c / (b ^ 2 + 2 * c ^ 2) + c * a / (c ^ 2 + 2 * a ^ 2) ≤ 1) := @solution
#print axioms solution
