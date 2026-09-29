-- Prove2me | solution 1 for WorkbookSource.base_42334
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:33:14.380476+00:00
-- url     : https://prove2.me/submissions/c951242c-099f-4ddb-b497-46b8b7af0c63

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (b + c) + b^2 / (c^2 + a^2) + 2 * c / (a + b)) ≥ 5 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4 - a^3*b - 5*a^3*c - 5*a^2*b^2 - a^2*b*c + 8*a^2*c^2 + 2*a*b^3 + 2*a*b^2*c - a*b*c^2 - 5*a*c^3 + 2*b^4 + 2*b^3*c - 5*b^2*c^2 - b*c^3 + 4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^2 * (b - a)^2 + (8 : ℝ) * a^2 * (c - b)^2 + (6 : ℝ) * a^1 * (b - a)^3 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^1 * (c - b)^3 + (2 : ℝ) * (b - a)^4 + (5 : ℝ) * (b - a)^3 * (c - b)^1 + (16 : ℝ) * (b - a)^2 * (c - b)^2 + (15 : ℝ) * (b - a)^1 * (c - b)^3 + (4 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4 - a^3*b - 5*a^3*c - 5*a^2*b^2 - a^2*b*c + 8*a^2*c^2 + 2*a*b^3 + 2*a*b^2*c - a*b*c^2 - 5*a*c^3 + 2*b^4 + 2*b^3*c - 5*b^2*c^2 - b*c^3 + 4*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^2 * (c - a)^2 + (16 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^2 * (b - c)^2 + (6 : ℝ) * a^1 * (c - a)^3 + (18 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (34 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^1 * (b - c)^3 + (2 : ℝ) * (c - a)^4 + (3 : ℝ) * (c - a)^3 * (b - c)^1 + (13 : ℝ) * (c - a)^2 * (b - c)^2 + (10 : ℝ) * (c - a)^1 * (b - c)^3 + (2 : ℝ) * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (4*a^4 - a^3*b - 5*a^3*c - 5*a^2*b^2 - a^2*b*c + 8*a^2*c^2 + 2*a*b^3 + 2*a*b^2*c - a*b*c^2 - 5*a*c^3 + 2*b^4 + 2*b^3*c - 5*b^2*c^2 - b*c^3 + 4*c^4) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * b^2 * (a - b)^2 + (16 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (8 : ℝ) * b^2 * (c - a)^2 + (20 : ℝ) * b^1 * (a - b)^3 + (30 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (30 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (10 : ℝ) * b^1 * (c - a)^3 + (6 : ℝ) * (a - b)^4 + (12 : ℝ) * (a - b)^3 * (c - a)^1 + (17 : ℝ) * (a - b)^2 * (c - a)^2 + (11 : ℝ) * (a - b)^1 * (c - a)^3 + (4 : ℝ) * (c - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4 - a^3*b - 5*a^3*c - 5*a^2*b^2 - a^2*b*c + 8*a^2*c^2 + 2*a*b^3 + 2*a*b^2*c - a*b*c^2 - 5*a*c^3 + 2*b^4 + 2*b^3*c - 5*b^2*c^2 - b*c^3 + 4*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (4*a^4 - a^3*b - 5*a^3*c - 5*a^2*b^2 - a^2*b*c + 8*a^2*c^2 + 2*a*b^3 + 2*a*b^2*c - a*b*c^2 - 5*a*c^3 + 2*b^4 + 2*b^3*c - 5*b^2*c^2 - b*c^3 + 4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a / (b + c) + b^2 / (c^2 + a^2) + 2 * c / (a + b)) ≥ 5 / 2) := @solution
#print axioms solution
