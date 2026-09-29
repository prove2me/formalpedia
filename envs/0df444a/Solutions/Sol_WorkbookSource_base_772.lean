-- Prove2me | solution 1 for WorkbookSource.base_772
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:19.26598+00:00
-- url     : https://prove2.me/submissions/7404558d-e5d1-41f1-a67a-cb7c41b0720f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / (c + a) + c / (a + b) + ((c / (a + b) + a / (b + c)) * (a / (b + c) + b / (c + a)))) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - a^2*b*c - a^2*c^2 - 2*a*b^2*c - 2*a*b*c^2 + b^4 + b^3*c + b*c^3 + c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^2 * (b - a)^2 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^2 * (c - b)^2 + (12 : ℝ) * a^1 * (b - a)^3 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^1 * (c - b)^3 + (4 : ℝ) * (b - a)^4 + (8 : ℝ) * (b - a)^3 * (c - b)^1 + (9 : ℝ) * (b - a)^2 * (c - b)^2 + (5 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - a^2*b*c - a^2*c^2 - 2*a*b^2*c - 2*a*b*c^2 + b^4 + b^3*c + b*c^3 + c^4) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * b^2 * (a - b)^2 + (3 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (6 : ℝ) * b^2 * (c - a)^2 + (7 : ℝ) * b^1 * (a - b)^3 + (7 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (11 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (5 : ℝ) * b^1 * (c - a)^3 + (2 : ℝ) * (a - b)^4 + (3 : ℝ) * (a - b)^3 * (c - a)^1 + (5 : ℝ) * (a - b)^2 * (c - a)^2 + (4 : ℝ) * (a - b)^1 * (c - a)^3 + (1 : ℝ) * (c - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - a^2*b*c - a^2*c^2 - 2*a*b^2*c - 2*a*b*c^2 + b^4 + b^3*c + b*c^3 + c^4) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * b^2 * (c - b)^2 + (9 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (9 : ℝ) * b^2 * (a - c)^2 + (7 : ℝ) * b^1 * (c - b)^3 + (14 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (18 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (6 : ℝ) * b^1 * (a - c)^3 + (2 : ℝ) * (c - b)^4 + (5 : ℝ) * (c - b)^3 * (a - c)^1 + (8 : ℝ) * (c - b)^2 * (a - c)^2 + (5 : ℝ) * (c - b)^1 * (a - c)^3 + (1 : ℝ) * (a - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4 + a^3*b + a^3*c - a^2*b^2 - a^2*b*c - a^2*c^2 - 2*a*b^2*c - 2*a*b*c^2 + b^4 + b^3*c + b*c^3 + c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ ((a + b + c)*(a^3 - a*b^2 - a*b*c - a*c^2 + b^3 + c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b / (c + a) + c / (a + b) + ((c / (a + b) + a / (b + c)) * (a / (b + c) + b / (c + a)))) ≥ 2) := @solution
#print axioms solution
