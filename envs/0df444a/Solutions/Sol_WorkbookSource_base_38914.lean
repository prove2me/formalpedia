-- Prove2me | solution 1 for WorkbookSource.base_38914
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:35.311676+00:00
-- url     : https://prove2.me/submissions/8c9a153f-d52d-4e43-9107-ed1ce42efab3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (b^2 - b * c + c^2) * (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥ a * b * c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 - 28*a^4*b*c/27 + a^4*c^2 - a^3*b^3 - a^3*b^2*c/9 - a^3*b*c^2/9 - a^3*c^3 + a^2*b^4 - a^2*b^3*c/9 + 7*a^2*b^2*c^2/9 - a^2*b*c^3/9 + a^2*c^4 - 28*a*b^4*c/27 - a*b^3*c^2/9 - a*b^2*c^3/9 - 28*a*b*c^4/27 + b^4*c^2 - b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (b - a)^2 + (5/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5/3 : ℝ) * a^4 * (c - b)^2 + (136/27 : ℝ) * a^3 * (b - a)^3 + (68/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (52/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (44/27 : ℝ) * a^3 * (c - b)^3 + (164/27 : ℝ) * a^2 * (b - a)^4 + (328/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (94/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (118/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (26/27 : ℝ) * a^2 * (c - b)^4 + (100/27 : ℝ) * a^1 * (b - a)^5 + (250/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (28/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (128/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (26/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (b - a)^6 + (3 : ℝ) * (b - a)^5 * (c - b)^1 + (4 : ℝ) * (b - a)^4 * (c - b)^2 + (3 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 - 28*a^4*b*c/27 + a^4*c^2 - a^3*b^3 - a^3*b^2*c/9 - a^3*b*c^2/9 - a^3*c^3 + a^2*b^4 - a^2*b^3*c/9 + 7*a^2*b^2*c^2/9 - a^2*b*c^3/9 + a^2*c^4 - 28*a*b^4*c/27 - a*b^3*c^2/9 - a*b^2*c^3/9 - 28*a*b*c^4/27 + b^4*c^2 - b^3*c^3 + b^2*c^4) := by
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
  have he : (a^4*b^2 - a^4*b*c + a^4*c^2 - a^3*b^3 - a^3*c^3 + a^2*b^4 + a^2*b^2*c^2 + a^2*c^4 - a*b^4*c - a*b*c^4 - a*b*c + b^4*c^2 - b^3*c^3 + b^2*c^4) = (a^4*b^2 - 28*a^4*b*c/27 + a^4*c^2 - a^3*b^3 - a^3*b^2*c/9 - a^3*b*c^2/9 - a^3*c^3 + a^2*b^4 - a^2*b^3*c/9 + 7*a^2*b^2*c^2/9 - a^2*b*c^3/9 + a^2*c^4 - 28*a*b^4*c/27 - a*b^3*c^2/9 - a*b^2*c^3/9 - 28*a*b*c^4/27 + b^4*c^2 - b^3*c^3 + b^2*c^4) := by
    linear_combination (a^3*b*c/27 + 2*a^2*b^2*c/27 + 2*a^2*b*c^2/27 + a^2*b*c/9 + a*b^3*c/27 + 2*a*b^2*c^2/27 + a*b^2*c/9 + a*b*c^3/27 + a*b*c^2/9 + a*b*c/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3), (b^2 - b * c + c^2) * (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥ a * b * c) := @solution
#print axioms solution
