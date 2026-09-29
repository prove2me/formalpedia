-- Prove2me | solution 1 for WorkbookSource.base_34132
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:15.574707+00:00
-- url     : https://prove2.me/submissions/54777297-6ad4-4f00-94bc-2ca8950d924e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) : 27 * a * b * c + 36 * (a * b + b * c + c * a) ≤ 13  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (13*a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 - 57*a*b*c + 3*a*c^2 + 13*b^3 + 3*b^2*c + 3*b*c^2 + 13*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (45 : ℝ) * a^1 * (b - a)^2 + (45 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (45 : ℝ) * a^1 * (c - b)^2 + (32 : ℝ) * (b - a)^3 + (48 : ℝ) * (b - a)^2 * (c - b)^1 + (42 : ℝ) * (b - a)^1 * (c - b)^2 + (13 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (13*a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 - 57*a*b*c + 3*a*c^2 + 13*b^3 + 3*b^2*c + 3*b*c^2 + 13*c^3) := by
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
  have he : (-27*a*b*c - 36*a*b - 36*a*c - 36*b*c + 13) = (13*a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 - 57*a*b*c + 3*a*c^2 + 13*b^3 + 3*b^2*c + 3*b*c^2 + 13*c^3) := by
    linear_combination (-13*a^2 + 10*a*b + 10*a*c - 13*a - 13*b^2 + 10*b*c - 13*b - 13*c^2 - 13*c - 13) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1), 27 * a * b * c + 36 * (a * b + b * c + c * a) ≤ 13) := @solution
#print axioms solution
