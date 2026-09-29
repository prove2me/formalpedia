-- Prove2me | solution 1 for WorkbookSource.base_50327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:59.979115+00:00
-- url     : https://prove2.me/submissions/ee89ac8f-61c8-49a2-99dc-e4e2e0ce82a3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b * c) / (a + b * c) + (b^2 + c * a) / (b + c * a) + (c^2 + a * b) / (c + a * b) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2/9 + 2*a^4*b*c/3 + a^4*c^2/9 + 2*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^4*c/3 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 2*a*b*c^4/3 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^4 * (b - a)^2 + (8/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8/3 : ℝ) * a^4 * (c - b)^2 + (68/9 : ℝ) * a^3 * (b - a)^3 + (34/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (10 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (28/9 : ℝ) * a^3 * (c - b)^3 + (68/9 : ℝ) * a^2 * (b - a)^4 + (136/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (14 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (58/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8/9 : ℝ) * a^2 * (c - b)^4 + (28/9 : ℝ) * a^1 * (b - a)^5 + (70/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (8 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (38/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * (b - a)^6 + (4/3 : ℝ) * (b - a)^5 * (c - b)^1 + (13/9 : ℝ) * (b - a)^4 * (c - b)^2 + (2/3 : ℝ) * (b - a)^3 * (c - b)^3 + (1/9 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2/9 + 2*a^4*b*c/3 + a^4*c^2/9 + 2*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^4*c/3 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 2*a*b*c^4/3 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
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
  have he : (a^4*b*c + a^3*b^2 - a^3*b*c + a^3*c^2 + a^2*b^3 - 2*a^2*b^2 + a^2*b*c + a^2*c^3 - 2*a^2*c^2 + a*b^4*c - a*b^3*c + a*b^2*c + a*b*c^4 - a*b*c^3 + a*b*c^2 - 3*a*b*c + b^3*c^2 + b^2*c^3 - 2*b^2*c^2) = (a^4*b^2/9 + 2*a^4*b*c/3 + a^4*c^2/9 + 2*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^4*c/3 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 2*a*b*c^4/3 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
    linear_combination (-a^3*b^2/9 + a^3*b*c/3 - a^3*c^2/9 - a^2*b^3/9 + 2*a^2*b^2*c/9 + 2*a^2*b^2/3 + 2*a^2*b*c^2/9 - a^2*c^3/9 + 2*a^2*c^2/3 + a*b^3*c/3 + 2*a*b^2*c^2/9 + a*b*c^3/3 + a*b*c - b^3*c^2/9 - b^2*c^3/9 + 2*b^2*c^2/3) * hab
  have hn : 0 ≤ (a^4*b*c + a^3*b^2 - a^3*b*c + a^3*c^2 + a^2*b^3 - 2*a^2*b^2 + a^2*b*c + a^2*c^3 - 2*a^2*c^2 + a*b^4*c - a*b^3*c + a*b^2*c + a*b*c^4 - a*b*c^3 + a*b*c^2 - 3*a*b*c + b^3*c^2 + b^2*c^3 - 2*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 + b * c) / (a + b * c) + (b^2 + c * a) / (b + c * a) + (c^2 + a * b) / (c + a * b) ≥ 3) := @solution
#print axioms solution
