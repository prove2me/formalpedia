-- Prove2me | solution 1 for WorkbookSource.plus_31943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:44:34.415767+00:00
-- url     : https://prove2.me/submissions/adf0e6bb-a431-4fdc-8be8-f27169a6082e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : a^3 + b^3 + c^3 + a^3 * b * c + a * b^3 * c + a * b * c^3 ≥ a * b * c / 3 + a^3 * b + a^3 * c + a * b^3 + b^3 * c + a * c^3 + b * c^3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5/4 - 3*a^3*b^2/4 + 5*a^3*b*c/4 - 3*a^3*c^2/4 - 3*a^2*b^3/4 - a^2*b^2*c/2 - a^2*b*c^2/2 - 3*a^2*c^3/4 + 5*a*b^3*c/4 - a*b^2*c^2/2 + 5*a*b*c^3/4 + 3*b^5/4 - 3*b^3*c^2/4 - 3*b^2*c^3/4 + 3*c^5/4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (17/4 : ℝ) * a^3 * (b - a)^2 + (17/4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (17/4 : ℝ) * a^3 * (c - b)^2 + (11/2 : ℝ) * a^2 * (b - a)^3 + (33/4 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (69/4 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (29/4 : ℝ) * a^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^4 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (67/4 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (59/4 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (15/4 : ℝ) * a^1 * (c - b)^4 + (9/2 : ℝ) * (b - a)^3 * (c - b)^2 + (27/4 : ℝ) * (b - a)^2 * (c - b)^3 + (15/4 : ℝ) * (b - a)^1 * (c - b)^4 + (3/4 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5/4 - 3*a^3*b^2/4 + 5*a^3*b*c/4 - 3*a^3*c^2/4 - 3*a^2*b^3/4 - a^2*b^2*c/2 - a^2*b*c^2/2 - 3*a^2*c^3/4 + 5*a*b^3*c/4 - a*b^2*c^2/2 + 5*a*b*c^3/4 + 3*b^5/4 - 3*b^3*c^2/4 - 3*b^2*c^3/4 + 3*c^5/4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (3*a^3*b*c - 3*a^3*b - 3*a^3*c + 3*a^3 + 3*a*b^3*c - 3*a*b^3 + 3*a*b*c^3 - a*b*c - 3*a*c^3 - 3*b^3*c + 3*b^3 - 3*b*c^3 + 3*c^3) = (3*a^5/4 - 3*a^3*b^2/4 + 5*a^3*b*c/4 - 3*a^3*c^2/4 - 3*a^2*b^3/4 - a^2*b^2*c/2 - a^2*b*c^2/2 - 3*a^2*c^3/4 + 5*a*b^3*c/4 - a*b^2*c^2/2 + 5*a*b*c^3/4 + 3*b^5/4 - 3*b^3*c^2/4 - 3*b^2*c^3/4 + 3*c^5/4) := by
    linear_combination (-3*a^4/4 + 3*a^3*b/4 + 3*a^3*c/4 - 3*a^3/2 + a^2*b*c/4 + 3*a*b^3/4 + a*b^2*c/4 + a*b*c^2/4 + a*b*c/2 + 3*a*c^3/4 - 3*b^4/4 + 3*b^3*c/4 - 3*b^3/2 + 3*b*c^3/4 - 3*c^4/4 - 3*c^3/2) * habc
  have hn : 0 ≤ (3*a^3*b*c - 3*a^3*b - 3*a^3*c + 3*a^3 + 3*a*b^3*c - 3*a*b^3 + 3*a*b*c^3 - a*b*c - 3*a*c^3 - 3*b^3*c + 3*b^3 - 3*b*c^3 + 3*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2), a^3 + b^3 + c^3 + a^3 * b * c + a * b^3 * c + a * b * c^3 ≥ a * b * c / 3 + a^3 * b + a^3 * c + a * b^3 + b^3 * c + a * c^3 + b * c^3) := @solution
#print axioms solution
