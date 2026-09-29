-- Prove2me | solution 1 for WorkbookSource.base_27521
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:21.034687+00:00
-- url     : https://prove2.me/submissions/0d9f9df3-ce93-4406-b3e8-fb9f4834c47f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a * b / (a * b + a + b) + b * c / (b * c + b + c) + c * a / (c * a + c + a) + 1 / 9 * ((a - b) ^ 2 / (a * b + a + b) + (b - c) ^ 2 / (b * c + b + c) + (c - a) ^ 2 / (c * a + c + a))) ≤ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/9 + a^5*c/9 + 5*a^4*b^2/9 + 8*a^4*b*c/9 + 5*a^4*c^2/9 + 8*a^3*b^3/9 + a^3*b^2*c/3 + a^3*b*c^2/3 + 8*a^3*c^3/9 + 5*a^2*b^4/9 + a^2*b^3*c/3 - 34*a^2*b^2*c^2/3 + a^2*b*c^3/3 + 5*a^2*c^4/9 + a*b^5/9 + 8*a*b^4*c/9 + a*b^3*c^2/3 + a*b^2*c^3/3 + 8*a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 5*b^4*c^2/9 + 8*b^3*c^3/9 + 5*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (106/3 : ℝ) * a^3 * (b - a)^3 + (53 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (43 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (38/3 : ℝ) * a^3 * (c - b)^3 + (334/9 : ℝ) * a^2 * (b - a)^4 + (668/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (187/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (227/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (28/9 : ℝ) * a^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^5 + (40 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (346/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (53/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (11/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/9 : ℝ) * a^1 * (c - b)^5 + (20/9 : ℝ) * (b - a)^6 + (20/3 : ℝ) * (b - a)^5 * (c - b)^1 + (23/3 : ℝ) * (b - a)^4 * (c - b)^2 + (38/9 : ℝ) * (b - a)^3 * (c - b)^3 + (10/9 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/9 + a^5*c/9 + 5*a^4*b^2/9 + 8*a^4*b*c/9 + 5*a^4*c^2/9 + 8*a^3*b^3/9 + a^3*b^2*c/3 + a^3*b*c^2/3 + 8*a^3*c^3/9 + 5*a^2*b^4/9 + a^2*b^3*c/3 - 34*a^2*b^2*c^2/3 + a^2*b*c^3/3 + 5*a^2*c^4/9 + a*b^5/9 + 8*a*b^4*c/9 + a*b^3*c^2/3 + a*b^2*c^3/3 + 8*a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 5*b^4*c^2/9 + 8*b^3*c^3/9 + 5*b^2*c^4/9 + b*c^5/9) := by
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
  have he : (-a^3*b^2*c - a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 2*a^3*b - a^3*c^2 - 2*a^3*c - a^2*b^3*c - a^2*b^3 - 12*a^2*b^2*c^2 - 12*a^2*b^2*c - a^2*b*c^3 - 12*a^2*b*c^2 + 4*a^2*b*c + 9*a^2*b - a^2*c^3 + 9*a^2*c - a*b^3*c^2 - 4*a*b^3*c - 2*a*b^3 - a*b^2*c^3 - 12*a*b^2*c^2 + 4*a*b^2*c + 9*a*b^2 - 4*a*b*c^3 + 4*a*b*c^2 + 18*a*b*c - 2*a*c^3 + 9*a*c^2 - b^3*c^2 - 2*b^3*c - b^2*c^3 + 9*b^2*c - 2*b*c^3 + 9*b*c^2) = (a^5*b/9 + a^5*c/9 + 5*a^4*b^2/9 + 8*a^4*b*c/9 + 5*a^4*c^2/9 + 8*a^3*b^3/9 + a^3*b^2*c/3 + a^3*b*c^2/3 + 8*a^3*c^3/9 + 5*a^2*b^4/9 + a^2*b^3*c/3 - 34*a^2*b^2*c^2/3 + a^2*b*c^3/3 + 5*a^2*c^4/9 + a*b^5/9 + 8*a*b^4*c/9 + a*b^3*c^2/3 + a*b^2*c^3/3 + 8*a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 5*b^4*c^2/9 + 8*b^3*c^3/9 + 5*b^2*c^4/9 + b*c^5/9) := by
    linear_combination (-a^4*b/9 - a^4*c/9 - 4*a^3*b^2/9 - 2*a^3*b*c/3 - a^3*b/3 - 4*a^3*c^2/9 - a^3*c/3 - 4*a^2*b^3/9 - 2*a^2*b^2*c/9 - 2*a^2*b^2 - 2*a^2*b*c^2/9 - 16*a^2*b*c/3 - 3*a^2*b - 4*a^2*c^3/9 - 2*a^2*c^2 - 3*a^2*c - a*b^4/9 - 2*a*b^3*c/3 - a*b^3/3 - 2*a*b^2*c^2/9 - 16*a*b^2*c/3 - 3*a*b^2 - 2*a*b*c^3/3 - 16*a*b*c^2/3 - 6*a*b*c - a*c^4/9 - a*c^3/3 - 3*a*c^2 - b^4*c/9 - 4*b^3*c^2/9 - b^3*c/3 - 4*b^2*c^3/9 - 2*b^2*c^2 - 3*b^2*c - b*c^4/9 - b*c^3/3 - 3*b*c^2) * habc
  have hn : 0 ≤ (-a^3*b^2*c - a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 2*a^3*b - a^3*c^2 - 2*a^3*c - a^2*b^3*c - a^2*b^3 - 12*a^2*b^2*c^2 - 12*a^2*b^2*c - a^2*b*c^3 - 12*a^2*b*c^2 + 4*a^2*b*c + 9*a^2*b - a^2*c^3 + 9*a^2*c - a*b^3*c^2 - 4*a*b^3*c - 2*a*b^3 - a*b^2*c^3 - 12*a*b^2*c^2 + 4*a*b^2*c + 9*a*b^2 - 4*a*b*c^3 + 4*a*b*c^2 + 18*a*b*c - 2*a*c^3 + 9*a*c^2 - b^3*c^2 - 2*b^3*c - b^2*c^3 + 9*b^2*c - 2*b*c^3 + 9*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a * b / (a * b + a + b) + b * c / (b * c + b + c) + c * a / (c * a + c + a) + 1 / 9 * ((a - b) ^ 2 / (a * b + a + b) + (b - c) ^ 2 / (b * c + b + c) + (c - a) ^ 2 / (c * a + c + a))) ≤ 1) := @solution
#print axioms solution
