-- Prove2me | solution 1 for WorkbookSource.plus_12136
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:52.407409+00:00
-- url     : https://prove2.me/submissions/d58c0d99-2cde-4355-90e2-f66f26c2602a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : a ^ 3 + b ^ 2 + c ^ 3 + a * b ^ 2 * c ≥ 4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (23*a^4/81 + 11*a^3*b/81 + 11*a^3*c/81 - 5*a^2*b^2/27 - 16*a^2*b*c/27 - 8*a^2*c^2/27 + 2*a*b^3/81 + 17*a*b^2*c/27 - 16*a*b*c^2/27 + 11*a*c^3/81 + 5*b^4/81 + 2*b^3*c/81 - 5*b^2*c^2/27 + 11*b*c^3/81 + 23*c^4/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13/9 : ℝ) * a^2 * (b - a)^2 + (19/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (13/9 : ℝ) * a^2 * (c - b)^2 + (40/27 : ℝ) * a^1 * (b - a)^3 + (31/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (11/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (38/27 : ℝ) * a^1 * (c - b)^3 + (26/81 : ℝ) * (b - a)^4 + (97/81 : ℝ) * (b - a)^3 * (c - b)^1 + (52/27 : ℝ) * (b - a)^2 * (c - b)^2 + (103/81 : ℝ) * (b - a)^1 * (c - b)^3 + (23/81 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (23*a^4/81 + 11*a^3*b/81 + 11*a^3*c/81 - 5*a^2*b^2/27 - 16*a^2*b*c/27 - 8*a^2*c^2/27 + 2*a*b^3/81 + 17*a*b^2*c/27 - 16*a*b*c^2/27 + 11*a*c^3/81 + 5*b^4/81 + 2*b^3*c/81 - 5*b^2*c^2/27 + 11*b*c^3/81 + 23*c^4/81) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (13/9 : ℝ) * a^2 * (c - a)^2 + (7/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (7/9 : ℝ) * a^2 * (b - c)^2 + (40/27 : ℝ) * a^1 * (c - a)^3 + (1 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (11/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (8/27 : ℝ) * a^1 * (b - c)^3 + (26/81 : ℝ) * (c - a)^4 + (7/81 : ℝ) * (c - a)^3 * (b - c)^1 + (7/27 : ℝ) * (c - a)^2 * (b - c)^2 + (22/81 : ℝ) * (c - a)^1 * (b - c)^3 + (5/81 : ℝ) * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (23*a^4/81 + 11*a^3*b/81 + 11*a^3*c/81 - 5*a^2*b^2/27 - 16*a^2*b*c/27 - 8*a^2*c^2/27 + 2*a*b^3/81 + 17*a*b^2*c/27 - 16*a*b*c^2/27 + 11*a*c^3/81 + 5*b^4/81 + 2*b^3*c/81 - 5*b^2*c^2/27 + 11*b*c^3/81 + 23*c^4/81) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (7/9 : ℝ) * b^2 * (a - b)^2 + (7/9 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (13/9 : ℝ) * b^2 * (c - a)^2 + (34/27 : ℝ) * b^1 * (a - b)^3 + (17/9 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (31/9 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (38/27 : ℝ) * b^1 * (c - a)^3 + (44/81 : ℝ) * (a - b)^4 + (88/81 : ℝ) * (a - b)^3 * (c - a)^1 + (49/27 : ℝ) * (a - b)^2 * (c - a)^2 + (103/81 : ℝ) * (a - b)^1 * (c - a)^3 + (23/81 : ℝ) * (c - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (23*a^4/81 + 11*a^3*b/81 + 11*a^3*c/81 - 5*a^2*b^2/27 - 16*a^2*b*c/27 - 8*a^2*c^2/27 + 2*a*b^3/81 + 17*a*b^2*c/27 - 16*a*b*c^2/27 + 11*a*c^3/81 + 5*b^4/81 + 2*b^3*c/81 - 5*b^2*c^2/27 + 11*b*c^3/81 + 23*c^4/81) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (a^3 + a*b^2*c + b^2 + c^3 - 4) = (23*a^4/81 + 11*a^3*b/81 + 11*a^3*c/81 - 5*a^2*b^2/27 - 16*a^2*b*c/27 - 8*a^2*c^2/27 + 2*a*b^3/81 + 17*a*b^2*c/27 - 16*a*b*c^2/27 + 11*a*c^3/81 + 5*b^4/81 + 2*b^3*c/81 - 5*b^2*c^2/27 + 11*b*c^3/81 + 23*c^4/81) := by
    linear_combination (-23*a^3/81 + 4*a^2*b/27 + 4*a^2*c/27 + 4*a^2/27 + a*b^2/27 + 8*a*b*c/27 + 8*a*b/27 + 4*a*c^2/27 + 8*a*c/27 + 4*a/9 - 5*b^3/81 + b^2*c/27 - 5*b^2/27 + 4*b*c^2/27 + 8*b*c/27 + 4*b/9 - 23*c^3/81 + 4*c^2/27 + 4*c/9 + 4/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3), a ^ 3 + b ^ 2 + c ^ 3 + a * b ^ 2 * c ≥ 4) := @solution
#print axioms solution
