-- Prove2me | solution 1 for WorkbookSource.base_26655
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:30:13.275001+00:00
-- url     : https://prove2.me/submissions/3e9cc9f0-d97c-4ba6-bcae-2371e9341bb8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 24 * (a * b * c) / (a + b) / (b + c) / (c + a) ≤ b * c + a * c + a * b  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3*b^2 - 2*a^3*b*c/3 + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 + a^2*c^3 - 2*a*b^3*c/3 - 4*a*b^2*c^2/3 - 2*a*b*c^3/3 + b^3*c^2 + b^2*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * a^3 * (b - a)^2 + (10/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (10/3 : ℝ) * a^3 * (c - b)^2 + (26/3 : ℝ) * a^2 * (b - a)^3 + (13 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (7 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (4/3 : ℝ) * a^2 * (c - b)^3 + (22/3 : ℝ) * a^1 * (b - a)^4 + (44/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (26/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (4/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (4 : ℝ) * (b - a)^3 * (c - b)^2 + (1 : ℝ) * (b - a)^2 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^2 - 2*a^3*b*c/3 + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 + a^2*c^3 - 2*a*b^3*c/3 - 4*a*b^2*c^2/3 - 2*a*b*c^3/3 + b^3*c^2 + b^2*c^3) := by
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
  have he : (a^3*b^2 + 2*a^3*b*c + a^3*c^2 + a^2*b^3 + 4*a^2*b^2*c + 4*a^2*b*c^2 + a^2*c^3 + 2*a*b^3*c + 4*a*b^2*c^2 + 2*a*b*c^3 - 24*a*b*c + b^3*c^2 + b^2*c^3) = (a^3*b^2 - 2*a^3*b*c/3 + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 + a^2*c^3 - 2*a*b^3*c/3 - 4*a*b^2*c^2/3 - 2*a*b*c^3/3 + b^3*c^2 + b^2*c^3) := by
    linear_combination (8*a^2*b*c/3 + 8*a*b^2*c/3 + 8*a*b*c^2/3 + 8*a*b*c) * habc
  have hn : 0 ≤ (a^3*b^2 + 2*a^3*b*c + a^3*c^2 + a^2*b^3 + 4*a^2*b^2*c + 4*a^2*b*c^2 + a^2*c^3 + 2*a*b^3*c + 4*a*b^2*c^2 + 2*a*b*c^3 - 24*a*b*c + b^3*c^2 + b^2*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 24 * (a * b * c) / (a + b) / (b + c) / (c + a) ≤ b * c + a * c + a * b) := @solution
#print axioms solution
