-- Prove2me | solution 1 for WorkbookSource.base_49525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:42.212552+00:00
-- url     : https://prove2.me/submissions/28333873-8d74-4e54-8959-eebc7dee821d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6) : 1 / a + 1 / b + 1 / c ≥ 21 / (a * b * c + 6)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b/36 + a^4*c/36 + a^3*b^2/12 - 7*a^3*b*c/18 + a^3*c^2/12 + a^2*b^3/12 + a^2*b^2*c/6 + a^2*b*c^2/6 + a^2*c^3/12 + a*b^4/36 - 7*a*b^3*c/18 + a*b^2*c^2/6 - 7*a*b*c^3/18 + a*c^4/36 + b^4*c/36 + b^3*c^2/12 + b^2*c^3/12 + b*c^4/36) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/6 : ℝ) * a^3 * (b - a)^2 + (1/6 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1/6 : ℝ) * a^3 * (c - b)^2 + (1/2 : ℝ) * a^2 * (b - a)^3 + (3/4 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1/4 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (5/9 : ℝ) * a^1 * (b - a)^4 + (10/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (2/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (1/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1/18 : ℝ) * a^1 * (c - b)^4 + (2/9 : ℝ) * (b - a)^5 + (5/9 : ℝ) * (b - a)^4 * (c - b)^1 + (1/2 : ℝ) * (b - a)^3 * (c - b)^2 + (7/36 : ℝ) * (b - a)^2 * (c - b)^3 + (1/36 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b/36 + a^4*c/36 + a^3*b^2/12 - 7*a^3*b*c/18 + a^3*c^2/12 + a^2*b^3/12 + a^2*b^2*c/6 + a^2*b*c^2/6 + a^2*c^3/12 + a*b^4/36 - 7*a*b^3*c/18 + a*b^2*c^2/6 - 7*a*b*c^3/18 + a*c^4/36 + b^4*c/36 + b^3*c^2/12 + b^2*c^3/12 + b*c^4/36) := by
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
  have he : (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 21*a*b*c + 6*a*b + 6*a*c + 6*b*c) = (a^4*b/36 + a^4*c/36 + a^3*b^2/12 - 7*a^3*b*c/18 + a^3*c^2/12 + a^2*b^3/12 + a^2*b^2*c/6 + a^2*b*c^2/6 + a^2*c^3/12 + a*b^4/36 - 7*a*b^3*c/18 + a*b^2*c^2/6 - 7*a*b*c^3/18 + a*c^4/36 + b^4*c/36 + b^3*c^2/12 + b^2*c^3/12 + b*c^4/36) := by
    linear_combination (-a^3*b/36 - a^3*c/36 - a^2*b^2/18 + 4*a^2*b*c/9 - a^2*b/6 - a^2*c^2/18 - a^2*c/6 - a*b^3/36 + 4*a*b^2*c/9 - a*b^2/6 + 4*a*b*c^2/9 + 3*a*b*c - a*b - a*c^3/36 - a*c^2/6 - a*c - b^3*c/36 - b^2*c^2/18 - b^2*c/6 - b*c^3/36 - b*c^2/6 - b*c) * habc
  have hn : 0 ≤ (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 21*a*b*c + 6*a*b + 6*a*c + 6*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6), 1 / a + 1 / b + 1 / c ≥ 21 / (a * b * c + 6)) := @solution
#print axioms solution
