-- Prove2me | solution 1 for WorkbookSource.plus_44318
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:35:53.643119+00:00
-- url     : https://prove2.me/submissions/b7c009f3-e144-4393-9900-f49f4d5408a8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a^2 * b + b^2 * c + c^2 * a + 2 * (a * b^2 + b * c^2 + c * a^2) + 3 * a * b * c ≤ 12   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^3/9 + a^2*b/3 - 2*a^2*c/3 - 2*a*b^2/3 - a*b*c/3 + a*c^2/3 + 4*b^3/9 + b^2*c/3 - 2*b*c^2/3 + 4*c^3/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^1 * (b - a)^2 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^1 * (c - b)^2 + (5/9 : ℝ) * (b - a)^3 + (1/3 : ℝ) * (b - a)^2 * (c - b)^1 + (2/3 : ℝ) * (b - a)^1 * (c - b)^2 + (4/9 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^3/9 + a^2*b/3 - 2*a^2*c/3 - 2*a*b^2/3 - a*b*c/3 + a*c^2/3 + 4*b^3/9 + b^2*c/3 - 2*b*c^2/3 + 4*c^3/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^1 * (c - a)^2 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (1 : ℝ) * a^1 * (b - c)^2 + (5/9 : ℝ) * (c - a)^3 + (4/3 : ℝ) * (c - a)^2 * (b - c)^1 + (5/3 : ℝ) * (c - a)^1 * (b - c)^2 + (4/9 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^3/9 + a^2*b/3 - 2*a^2*c/3 - 2*a*b^2/3 - a*b*c/3 + a*c^2/3 + 4*b^3/9 + b^2*c/3 - 2*b*c^2/3 + 4*c^3/9) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^2*b - 2*a^2*c - 2*a*b^2 - 3*a*b*c - a*c^2 - b^2*c - 2*b*c^2 + 12) = (4*a^3/9 + a^2*b/3 - 2*a^2*c/3 - 2*a*b^2/3 - a*b*c/3 + a*c^2/3 + 4*b^3/9 + b^2*c/3 - 2*b*c^2/3 + 4*c^3/9) := by
    linear_combination (-4*a^2/9 - 8*a*b/9 - 8*a*c/9 - 4*a/3 - 4*b^2/9 - 8*b*c/9 - 4*b/3 - 4*c^2/9 - 4*c/3 - 4) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), a^2 * b + b^2 * c + c^2 * a + 2 * (a * b^2 + b * c^2 + c * a^2) + 3 * a * b * c ≤ 12) := @solution
#print axioms solution
