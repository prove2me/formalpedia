-- Prove2me | solution 1 for WorkbookSource.base_12712
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:46:36.770914+00:00
-- url     : https://prove2.me/submissions/c7332ae1-edbb-406e-9c08-1f5461be60d4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 + a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b)) ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c - 3*a^4*b*c + 2*a^4*c^2 + a^3*b^3 + a^3*b*c^2 + a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a*b^5 - 3*a*b^4*c + a*b^2*c^3 - 3*a*b*c^4 + b^3*c^3 + 2*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^4 * (b - a)^2 + (10 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (10 : ℝ) * a^4 * (c - b)^2 + (31 : ℝ) * a^3 * (b - a)^3 + (60 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (47 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^3 * (c - b)^3 + (37 : ℝ) * a^2 * (b - a)^4 + (101 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (99 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (35 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^5 + (68 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (85 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (46 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (11 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (16 : ℝ) * (b - a)^5 * (c - b)^1 + (25 : ℝ) * (b - a)^4 * (c - b)^2 + (19 : ℝ) * (b - a)^3 * (c - b)^3 + (7 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c - 3*a^4*b*c + 2*a^4*c^2 + a^3*b^3 + a^3*b*c^2 + a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a*b^5 - 3*a*b^4*c + a*b^2*c^3 - 3*a*b*c^4 + b^3*c^3 + 2*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^4 * (c - a)^2 + (10 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (10 : ℝ) * a^4 * (b - c)^2 + (31 : ℝ) * a^3 * (c - a)^3 + (33 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (20 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (9 : ℝ) * a^3 * (b - c)^3 + (37 : ℝ) * a^2 * (c - a)^4 + (47 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (18 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (8 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (20 : ℝ) * a^1 * (c - a)^5 + (32 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (13 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1 : ℝ) * a^1 * (b - c)^5 + (4 : ℝ) * (c - a)^6 + (8 : ℝ) * (c - a)^5 * (b - c)^1 + (5 : ℝ) * (c - a)^4 * (b - c)^2 + (1 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c - 3*a^4*b*c + 2*a^4*c^2 + a^3*b^3 + a^3*b*c^2 + a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a*b^5 - 3*a*b^4*c + a*b^2*c^3 - 3*a*b*c^4 + b^3*c^3 + 2*b^2*c^4 + b*c^5) := by
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
  have hn : 0 ≤ (a^5*c - 3*a^4*b*c + 2*a^4*c^2 + a^3*b^3 + a^3*b*c^2 + a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a*b^5 - 3*a*b^4*c + a*b^2*c^3 - 3*a*b*c^4 + b^3*c^3 + 2*b^2*c^4 + b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 + a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b)) ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b))) := @solution
#print axioms solution
