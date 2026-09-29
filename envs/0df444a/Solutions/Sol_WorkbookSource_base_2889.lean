-- Prove2me | solution 1 for WorkbookSource.base_2889
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:17.576349+00:00
-- url     : https://prove2.me/submissions/c101761d-cdc7-41fc-a969-c5325146794a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 + a^4*b - a^3*c^2 - a^2*b^3 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + a*c^4 + b^5 + b^4*c - b^2*c^3 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^3 * (b - a)^2 + (10 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (10 : ℝ) * a^3 * (c - b)^2 + (17 : ℝ) * a^2 * (b - a)^3 + (21 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (30 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (13 : ℝ) * a^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^4 + (14 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (22 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (3 : ℝ) * (b - a)^4 * (c - b)^1 + (7 : ℝ) * (b - a)^3 * (c - b)^2 + (9 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5 + a^4*b - a^3*c^2 - a^2*b^3 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + a*c^4 + b^5 + b^4*c - b^2*c^3 + c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^3 * (c - a)^2 + (10 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (10 : ℝ) * a^3 * (b - c)^2 + (17 : ℝ) * a^2 * (c - a)^3 + (30 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (39 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (13 : ℝ) * a^2 * (b - c)^3 + (10 : ℝ) * a^1 * (c - a)^4 + (26 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (44 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (28 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^1 * (b - c)^4 + (2 : ℝ) * (c - a)^5 + (7 : ℝ) * (c - a)^4 * (b - c)^1 + (15 : ℝ) * (c - a)^3 * (b - c)^2 + (14 : ℝ) * (c - a)^2 * (b - c)^3 + (6 : ℝ) * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 + a^4*b - a^3*c^2 - a^2*b^3 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + a*c^4 + b^5 + b^4*c - b^2*c^3 + c^5) := by
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
  have hn : 0 ≤ (a^5 + a^4*b - a^3*c^2 - a^2*b^3 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + a*c^4 + b^5 + b^4*c - b^2*c^3 + c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≥ 4) := @solution
#print axioms solution
