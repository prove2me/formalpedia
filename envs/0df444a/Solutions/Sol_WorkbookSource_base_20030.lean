-- Prove2me | solution 1 for WorkbookSource.base_20030
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:44.605086+00:00
-- url     : https://prove2.me/submissions/95283aad-005e-4607-8706-d1f6e7d707de

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : (a + b + 1) * (b + c + 1) * (c + a + 1) ≤ 27  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (11*a^3/27 - a^2*b/9 - a^2*c/9 - a*b^2/9 - 5*a*b*c/9 - a*c^2/9 + 11*b^3/27 - b^2*c/9 - b*c^2/9 + 11*c^3/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^1 * (b - a)^2 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^1 * (c - b)^2 + (16/27 : ℝ) * (b - a)^3 + (8/9 : ℝ) * (b - a)^2 * (c - b)^1 + (10/9 : ℝ) * (b - a)^1 * (c - b)^2 + (11/27 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (11*a^3/27 - a^2*b/9 - a^2*c/9 - a*b^2/9 - 5*a*b*c/9 - a*c^2/9 + 11*b^3/27 - b^2*c/9 - b*c^2/9 + 11*c^3/27) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^2*b - a^2*c - a^2 - a*b^2 - 2*a*b*c - 3*a*b - a*c^2 - 3*a*c - 2*a - b^2*c - b^2 - b*c^2 - 3*b*c - 2*b - c^2 - 2*c + 26) = (11*a^3/27 - a^2*b/9 - a^2*c/9 - a*b^2/9 - 5*a*b*c/9 - a*c^2/9 + 11*b^3/27 - b^2*c/9 - b*c^2/9 + 11*c^3/27) := by
    linear_combination (-11*a^2/27 - 13*a*b/27 - 13*a*c/27 - 20*a/9 - 11*b^2/27 - 13*b*c/27 - 20*b/9 - 11*c^2/27 - 20*c/9 - 26/3) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), (a + b + 1) * (b + c + 1) * (c + a + 1) ≤ 27) := @solution
#print axioms solution
