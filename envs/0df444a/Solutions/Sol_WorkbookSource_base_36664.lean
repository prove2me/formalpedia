-- Prove2me | solution 1 for WorkbookSource.base_36664
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:21:21.299739+00:00
-- url     : https://prove2.me/submissions/a39c97f3-1485-47ff-bc62-785ec8141bf0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : a^2 + b^3 + c^3 ≥ 28 / 27  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^3 + 3*a^2*b + 3*a^2*c - 21*a*b^2/2 - 21*a*b*c - 21*a*c^2/2 + 47*b^3/2 - 21*b^2*c/2 - 21*b*c^2/2 + 47*c^3/2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^1 * (b - a)^2 + (36 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (99/2 : ℝ) * a^1 * (c - b)^2 + (26 : ℝ) * (b - a)^3 + (39 : ℝ) * (b - a)^2 * (c - b)^1 + (60 : ℝ) * (b - a)^1 * (c - b)^2 + (47/2 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (10*a^3 + 3*a^2*b + 3*a^2*c - 21*a*b^2/2 - 21*a*b*c - 21*a*c^2/2 + 47*b^3/2 - 21*b^2*c/2 - 21*b*c^2/2 + 47*c^3/2) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (99/2 : ℝ) * b^1 * (a - b)^2 + (63 : ℝ) * b^1 * (a - b)^1 * (c - a)^1 + (99/2 : ℝ) * b^1 * (c - a)^2 + (26 : ℝ) * (a - b)^3 + (105/2 : ℝ) * (a - b)^2 * (c - a)^1 + (60 : ℝ) * (a - b)^1 * (c - a)^2 + (47/2 : ℝ) * (c - a)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (10*a^3 + 3*a^2*b + 3*a^2*c - 21*a*b^2/2 - 21*a*b*c - 21*a*c^2/2 + 47*b^3/2 - 21*b^2*c/2 - 21*b*c^2/2 + 47*c^3/2) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (99/2 : ℝ) * b^1 * (c - b)^2 + (36 : ℝ) * b^1 * (c - b)^1 * (a - c)^1 + (36 : ℝ) * b^1 * (a - c)^2 + (26 : ℝ) * (c - b)^3 + (51/2 : ℝ) * (c - b)^2 * (a - c)^1 + (33 : ℝ) * (c - b)^1 * (a - c)^2 + (10 : ℝ) * (a - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^3 + 3*a^2*b + 3*a^2*c - 21*a*b^2/2 - 21*a*b*c - 21*a*c^2/2 + 47*b^3/2 - 21*b^2*c/2 - 21*b*c^2/2 + 47*c^3/2) := by
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
  have he : (27*a^2 + 27*b^3 + 27*c^3 - 28) = (10*a^3 + 3*a^2*b + 3*a^2*c - 21*a*b^2/2 - 21*a*b*c - 21*a*c^2/2 + 47*b^3/2 - 21*b^2*c/2 - 21*b*c^2/2 + 47*c^3/2) := by
    linear_combination (-10*a^2 + 7*a*b + 7*a*c + 7*a + 7*b^2/2 + 7*b*c + 7*b + 7*c^2/2 + 7*c + 14) * habc
  have hn : 0 ≤ (27*a^2 + 27*b^3 + 27*c^3 - 28) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2), a^2 + b^3 + c^3 ≥ 28 / 27) := @solution
#print axioms solution
