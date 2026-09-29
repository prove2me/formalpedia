-- Prove2me | solution 1 for WorkbookSource.base_31287
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:26:58.391664+00:00
-- url     : https://prove2.me/submissions/4f922acb-04d6-42e5-b212-723cfe4f5ec5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / b + b^2 / c + c^2 / a + a + b + c ≥ 2 * (a + b + c)^3 / (3 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c + 3*a^4*c^2 - 3*a^3*b^2*c + 3*a^2*b^4 - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + a*b^4*c - 3*a*b^3*c^2 + a*b*c^4 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (35 : ℝ) * a^3 * (b - a)^3 + (66 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (57 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (13 : ℝ) * a^3 * (c - b)^3 + (37 : ℝ) * a^2 * (b - a)^4 + (101 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (41 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (17 : ℝ) * a^1 * (b - a)^5 + (59 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (75 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (40 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (18 : ℝ) * (b - a)^4 * (c - b)^2 + (12 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c + 3*a^4*c^2 - 3*a^3*b^2*c + 3*a^2*b^4 - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + a*b^4*c - 3*a*b^3*c^2 + a*b*c^4 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (c - a)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^4 * (b - c)^2 + (35 : ℝ) * a^3 * (c - a)^3 + (39 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (30 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (13 : ℝ) * a^3 * (b - c)^3 + (37 : ℝ) * a^2 * (c - a)^4 + (47 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (24 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (14 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (17 : ℝ) * a^1 * (c - a)^5 + (26 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * (c - a)^6 + (6 : ℝ) * (c - a)^5 * (b - c)^1 + (3 : ℝ) * (c - a)^4 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c + 3*a^4*c^2 - 3*a^3*b^2*c + 3*a^2*b^4 - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + a*b^4*c - 3*a*b^3*c^2 + a*b*c^4 + 3*b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b*c + 3*a^4*c^2 - 3*a^3*b^2*c + 3*a^2*b^4 - 3*a^2*b^2*c^2 - 3*a^2*b*c^3 + a*b^4*c - 3*a*b^3*c^2 + a*b*c^4 + 3*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 / b + b^2 / c + c^2 / a + a + b + c ≥ 2 * (a + b + c)^3 / (3 * (a * b + b * c + c * a))) := @solution
#print axioms solution
