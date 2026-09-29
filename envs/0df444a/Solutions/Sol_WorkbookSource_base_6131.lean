-- Prove2me | solution 1 for WorkbookSource.base_6131
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:44.985682+00:00
-- url     : https://prove2.me/submissions/16241969-2d82-4e07-95d5-9580fe641559

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a * b + c) / (a + b) + (b * c + a) / (b + c) + (c * a + b) / (c + a) ≥ 11 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4/3 - a^3*b - a^3*c - 2*a^2*b^2/3 + 4*a^2*b*c - 2*a^2*c^2/3 - a*b^3 + 4*a*b^2*c + 4*a*b*c^2 - a*c^3 + 4*b^4/3 - b^3*c - 2*b^2*c^2/3 - b*c^3 + 4*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 + (64/3 : ℝ) * a^3 * (b - a)^1 + (32/3 : ℝ) * a^3 * (c - b)^1 + (62/3 : ℝ) * a^2 * (b - a)^2 + (62/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (14/3 : ℝ) * a^2 * (c - b)^2 + (6 : ℝ) * a^1 * (b - a)^3 + (9 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (29/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (10/3 : ℝ) * a^1 * (c - b)^3 + (13/3 : ℝ) * (b - a)^2 * (c - b)^2 + (13/3 : ℝ) * (b - a)^1 * (c - b)^3 + (4/3 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4/3 - a^3*b - a^3*c - 2*a^2*b^2/3 + 4*a^2*b*c - 2*a^2*c^2/3 - a*b^3 + 4*a*b^2*c + 4*a*b*c^2 - a*c^3 + 4*b^4/3 - b^3*c - 2*b^2*c^2/3 - b*c^3 + 4*c^4/3) := by
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
  have he : (4*a^3 + 4*a^2*b^2 + 12*a^2*b*c - 7*a^2*b + 4*a^2*c^2 - 7*a^2*c + 12*a*b^2*c - 7*a*b^2 + 12*a*b*c^2 - 10*a*b*c - 7*a*c^2 + 4*b^3 + 4*b^2*c^2 - 7*b^2*c - 7*b*c^2 + 4*c^3) = (4*a^4/3 - a^3*b - a^3*c - 2*a^2*b^2/3 + 4*a^2*b*c - 2*a^2*c^2/3 - a*b^3 + 4*a*b^2*c + 4*a*b*c^2 - a*c^3 + 4*b^4/3 - b^3*c - 2*b^2*c^2/3 - b*c^3 + 4*c^4/3) := by
    linear_combination (-4*a^3/3 + 7*a^2*b/3 + 7*a^2*c/3 + 7*a*b^2/3 + 10*a*b*c/3 + 7*a*c^2/3 - 4*b^3/3 + 7*b^2*c/3 + 7*b*c^2/3 - 4*c^3/3) * habc
  have hn : 0 ≤ (4*a^3 + 4*a^2*b^2 + 12*a^2*b*c - 7*a^2*b + 4*a^2*c^2 - 7*a^2*c + 12*a*b^2*c - 7*a*b^2 + 12*a*b*c^2 - 10*a*b*c - 7*a*c^2 + 4*b^3 + 4*b^2*c^2 - 7*b^2*c - 7*b*c^2 + 4*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a * b + c) / (a + b) + (b * c + a) / (b + c) + (c * a + b) / (c + a) ≥ 11 / 4) := @solution
#print axioms solution
