-- Prove2me | solution 1 for WorkbookSource.base_10232
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:36.773318+00:00
-- url     : https://prove2.me/submissions/4104b8c9-0ec4-401b-b8bd-a2a518727f4f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) :  (a^2 + b^2 + c^2 + a * b * c - 3) * (2 + a * b * c) ≥ 3  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 - a^4*b^2/81 + 2*a^4*b*c/9 - a^4*c^2/81 - 4*a^3*b^3/81 - 10*a^3*b^2*c/81 - 10*a^3*b*c^2/81 - 4*a^3*c^3/81 - a^2*b^4/81 - 10*a^2*b^3*c/81 + a^2*b^2*c^2/9 - 10*a^2*b*c^3/81 - a^2*c^4/81 + 2*a*b^5/81 + 2*a*b^4*c/9 - 10*a*b^3*c^2/81 - 10*a*b^2*c^3/81 + 2*a*b*c^4/9 + 2*a*c^5/81 + b^6/81 + 2*b^5*c/81 - b^4*c^2/81 - 4*b^3*c^3/81 - b^2*c^4/81 + 2*b*c^5/81 + c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^4 * (b - a)^2 + (2/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^4 * (c - b)^2 + (40/27 : ℝ) * a^3 * (b - a)^3 + (20/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (28/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (32/27 : ℝ) * a^3 * (c - b)^3 + (29/27 : ℝ) * a^2 * (b - a)^4 + (58/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (37/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (82/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (17/27 : ℝ) * a^2 * (c - b)^4 + (20/81 : ℝ) * a^1 * (b - a)^5 + (50/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (152/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (178/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (76/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10/81 : ℝ) * a^1 * (c - b)^5 + (16/81 : ℝ) * (b - a)^4 * (c - b)^2 + (32/81 : ℝ) * (b - a)^3 * (c - b)^3 + (8/27 : ℝ) * (b - a)^2 * (c - b)^4 + (8/81 : ℝ) * (b - a)^1 * (c - b)^5 + (1/81 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 - a^4*b^2/81 + 2*a^4*b*c/9 - a^4*c^2/81 - 4*a^3*b^3/81 - 10*a^3*b^2*c/81 - 10*a^3*b*c^2/81 - 4*a^3*c^3/81 - a^2*b^4/81 - 10*a^2*b^3*c/81 + a^2*b^2*c^2/9 - 10*a^2*b*c^3/81 - a^2*c^4/81 + 2*a*b^5/81 + 2*a*b^4*c/9 - 10*a*b^3*c^2/81 - 10*a*b^2*c^3/81 + 2*a*b*c^4/9 + 2*a*c^5/81 + b^6/81 + 2*b^5*c/81 - b^4*c^2/81 - 4*b^3*c^3/81 - b^2*c^4/81 + 2*b*c^5/81 + c^6/81) := by
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
  have he : (a^3*b*c + a^2*b^2*c^2 + 2*a^2 + a*b^3*c + a*b*c^3 - a*b*c + 2*b^2 + 2*c^2 - 9) = (a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 - a^4*b^2/81 + 2*a^4*b*c/9 - a^4*c^2/81 - 4*a^3*b^3/81 - 10*a^3*b^2*c/81 - 10*a^3*b*c^2/81 - 4*a^3*c^3/81 - a^2*b^4/81 - 10*a^2*b^3*c/81 + a^2*b^2*c^2/9 - 10*a^2*b*c^3/81 - a^2*c^4/81 + 2*a*b^5/81 + 2*a*b^4*c/9 - 10*a*b^3*c^2/81 - 10*a*b^2*c^3/81 + 2*a*b*c^4/9 + 2*a*c^5/81 + b^6/81 + 2*b^5*c/81 - b^4*c^2/81 - 4*b^3*c^3/81 - b^2*c^4/81 + 2*b*c^5/81 + c^6/81) := by
    linear_combination (-a^5/81 - a^4*b/81 - a^4*c/81 - a^4/27 + 2*a^3*b^2/81 - 16*a^3*b*c/81 + 2*a^3*c^2/81 - a^3/9 + 2*a^2*b^3/81 + 8*a^2*b^2*c/27 + 2*a^2*b^2/27 + 8*a^2*b*c^2/27 + 11*a^2*b*c/27 + a^2*b/9 + 2*a^2*c^3/81 + 2*a^2*c^2/27 + a^2*c/9 - a^2/3 - a*b^4/81 - 16*a*b^3*c/81 + 8*a*b^2*c^2/27 + 11*a*b^2*c/27 + a*b^2/9 - 16*a*b*c^3/81 + 11*a*b*c^2/27 + a*b*c + 2*a*b/3 - a*c^4/81 + a*c^2/9 + 2*a*c/3 + a - b^5/81 - b^4*c/81 - b^4/27 + 2*b^3*c^2/81 - b^3/9 + 2*b^2*c^3/81 + 2*b^2*c^2/27 + b^2*c/9 - b^2/3 - b*c^4/81 + b*c^2/9 + 2*b*c/3 + b - c^5/81 - c^4/27 - c^3/9 - c^2/3 + c + 3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3), (a^2 + b^2 + c^2 + a * b * c - 3) * (2 + a * b * c) ≥ 3) := @solution
#print axioms solution
