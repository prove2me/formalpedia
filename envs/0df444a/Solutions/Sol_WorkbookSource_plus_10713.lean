-- Prove2me | solution 1 for WorkbookSource.plus_10713
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:51.657886+00:00
-- url     : https://prove2.me/submissions/690c66dd-f6d4-4121-a0bb-e9763056c39b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^2 + b^2 + c^2)^3 ≤ 3 * (a^3 + b^3 + c^3)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 - 3*a^4*b^2 - 3*a^4*c^2 + 6*a^3*b^3 + 6*a^3*c^3 - 3*a^2*b^4 - 6*a^2*b^2*c^2 - 3*a^2*c^4 + 2*b^6 - 3*b^4*c^2 + 6*b^3*c^3 - 3*b^2*c^4 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^4 * (b - a)^2 + (18 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^4 * (c - b)^2 + (44 : ℝ) * a^3 * (b - a)^3 + (66 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (78 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (28 : ℝ) * a^3 * (c - b)^3 + (48 : ℝ) * a^2 * (b - a)^4 + (96 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (138 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (90 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (108 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (102 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (54 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (27 : ℝ) * (b - a)^4 * (c - b)^2 + (34 : ℝ) * (b - a)^3 * (c - b)^3 + (27 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 - 3*a^4*b^2 - 3*a^4*c^2 + 6*a^3*b^3 + 6*a^3*c^3 - 3*a^2*b^4 - 6*a^2*b^2*c^2 - 3*a^2*c^4 + 2*b^6 - 3*b^4*c^2 + 6*b^3*c^3 - 3*b^2*c^4 + 2*c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a^2 + b^2 + c^2)^3 ≤ 3 * (a^3 + b^3 + c^3)^2) := @solution
#print axioms solution
