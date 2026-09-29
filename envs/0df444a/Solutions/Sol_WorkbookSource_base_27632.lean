-- Prove2me | solution 1 for WorkbookSource.base_27632
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:22.407752+00:00
-- url     : https://prove2.me/submissions/feeb58f8-c041-4333-8b71-6b5995aac568

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 2 / a + 2 / b + 2 / c + 2 * (a * b + b * c + c * a) ≥ 12  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b/27 + 2*a^4*c/27 + 2*a^3*b^2/9 - 22*a^3*b*c/27 + 2*a^3*c^2/9 + 2*a^2*b^3/9 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 + 2*a^2*c^3/9 + 2*a*b^4/27 - 22*a*b^3*c/27 + 2*a*b^2*c^2/9 - 22*a*b*c^3/27 + 2*a*c^4/27 + 2*b^4*c/27 + 2*b^3*c^2/9 + 2*b^2*c^3/9 + 2*b*c^4/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^3 * (b - a)^2 + (2/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^3 * (c - b)^2 + (16/9 : ℝ) * a^2 * (b - a)^3 + (8/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (4/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (2/9 : ℝ) * a^2 * (c - b)^3 + (46/27 : ℝ) * a^1 * (b - a)^4 + (92/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (20/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (14/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (4/27 : ℝ) * a^1 * (c - b)^4 + (16/27 : ℝ) * (b - a)^5 + (40/27 : ℝ) * (b - a)^4 * (c - b)^1 + (4/3 : ℝ) * (b - a)^3 * (c - b)^2 + (14/27 : ℝ) * (b - a)^2 * (c - b)^3 + (2/27 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b/27 + 2*a^4*c/27 + 2*a^3*b^2/9 - 22*a^3*b*c/27 + 2*a^3*c^2/9 + 2*a^2*b^3/9 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 + 2*a^2*c^3/9 + 2*a*b^4/27 - 22*a*b^3*c/27 + 2*a*b^2*c^2/9 - 22*a*b*c^3/27 + 2*a*c^4/27 + 2*b^4*c/27 + 2*b^3*c^2/9 + 2*b^2*c^3/9 + 2*b*c^4/27) := by
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
  have he : (2*a^2*b^2*c + 2*a^2*b*c^2 + 2*a*b^2*c^2 - 12*a*b*c + 2*a*b + 2*a*c + 2*b*c) = (2*a^4*b/27 + 2*a^4*c/27 + 2*a^3*b^2/9 - 22*a^3*b*c/27 + 2*a^3*c^2/9 + 2*a^2*b^3/9 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 + 2*a^2*c^3/9 + 2*a*b^4/27 - 22*a*b^3*c/27 + 2*a*b^2*c^2/9 - 22*a*b*c^3/27 + 2*a*c^4/27 + 2*b^4*c/27 + 2*b^3*c^2/9 + 2*b^2*c^3/9 + 2*b*c^4/27) := by
    linear_combination (-2*a^3*b/27 - 2*a^3*c/27 - 4*a^2*b^2/27 + 26*a^2*b*c/27 - 2*a^2*b/9 - 4*a^2*c^2/27 - 2*a^2*c/9 - 2*a*b^3/27 + 26*a*b^2*c/27 - 2*a*b^2/9 + 26*a*b*c^2/27 + 10*a*b*c/3 - 2*a*b/3 - 2*a*c^3/27 - 2*a*c^2/9 - 2*a*c/3 - 2*b^3*c/27 - 4*b^2*c^2/27 - 2*b^2*c/9 - 2*b*c^3/27 - 2*b*c^2/9 - 2*b*c/3) * hab
  have hn : 0 ≤ (2*a^2*b^2*c + 2*a^2*b*c^2 + 2*a*b^2*c^2 - 12*a*b*c + 2*a*b + 2*a*c + 2*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 2 / a + 2 / b + 2 / c + 2 * (a * b + b * c + c * a) ≥ 12) := @solution
#print axioms solution
