-- Prove2me | solution 1 for WorkbookSource.base_53905
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:34.771589+00:00
-- url     : https://prove2.me/submissions/7420fa82-ca26-4fcb-aafc-1f5359c15318

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a ^ 2 + b + c) + 1 / (b ^ 2 + a + c) + 1 / (c ^ 2 + a + b) ≤ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - 2*a^4*b*c/27 + 8*a^4*c^2/81 + 16*a^3*b^3/81 - 19*a^3*b^2*c/81 - 19*a^3*b*c^2/81 + 16*a^3*c^3/81 + 8*a^2*b^4/81 - 19*a^2*b^3*c/81 + 2*a^2*b^2*c^2/9 - 19*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - 2*a*b^4*c/27 - 19*a*b^3*c^2/81 - 19*a*b^2*c^3/81 - 2*a*b*c^4/27 + 2*a*c^5/81 + 2*b^6/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 16*b^3*c^3/81 + 8*b^2*c^4/81 + 2*b*c^5/81 + 2*c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4/3 : ℝ) * a^4 * (b - a)^2 + (4/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4/3 : ℝ) * a^4 * (c - b)^2 + (106/27 : ℝ) * a^3 * (b - a)^3 + (53/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (43/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (38/27 : ℝ) * a^3 * (c - b)^3 + (122/27 : ℝ) * a^2 * (b - a)^4 + (244/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (73/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (97/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (20/27 : ℝ) * a^2 * (c - b)^4 + (194/81 : ℝ) * a^1 * (b - a)^5 + (485/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (524/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (301/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (100/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (16/81 : ℝ) * a^1 * (c - b)^5 + (40/81 : ℝ) * (b - a)^6 + (40/27 : ℝ) * (b - a)^5 * (c - b)^1 + (154/81 : ℝ) * (b - a)^4 * (c - b)^2 + (4/3 : ℝ) * (b - a)^3 * (c - b)^3 + (16/27 : ℝ) * (b - a)^2 * (c - b)^4 + (14/81 : ℝ) * (b - a)^1 * (c - b)^5 + (2/81 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - 2*a^4*b*c/27 + 8*a^4*c^2/81 + 16*a^3*b^3/81 - 19*a^3*b^2*c/81 - 19*a^3*b*c^2/81 + 16*a^3*c^3/81 + 8*a^2*b^4/81 - 19*a^2*b^3*c/81 + 2*a^2*b^2*c^2/9 - 19*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - 2*a*b^4*c/27 - 19*a*b^3*c^2/81 - 19*a*b^2*c^3/81 - 2*a*b*c^4/27 + 2*a*c^5/81 + 2*b^6/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 16*b^3*c^3/81 + 8*b^2*c^4/81 + 2*b*c^5/81 + 2*c^6/81) := by
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
  have he : (a^4 + a^3*b^2 + a^3*b + a^3*c^2 + a^3*c - 2*a^3 + a^2*b^3 + a^2*b^2*c^2 - a^2*b^2 + a^2*b*c + a^2*c^3 - a^2*c^2 - a^2 + a*b^3 + a*b^2*c + a*b*c^2 + 2*a*b*c - 3*a*b + a*c^3 - 3*a*c + b^4 + b^3*c^2 + b^3*c - 2*b^3 + b^2*c^3 - b^2*c^2 - b^2 + b*c^3 - 3*b*c + c^4 - 2*c^3 - c^2) = (2*a^6/81 + 2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - 2*a^4*b*c/27 + 8*a^4*c^2/81 + 16*a^3*b^3/81 - 19*a^3*b^2*c/81 - 19*a^3*b*c^2/81 + 16*a^3*c^3/81 + 8*a^2*b^4/81 - 19*a^2*b^3*c/81 + 2*a^2*b^2*c^2/9 - 19*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - 2*a*b^4*c/27 - 19*a*b^3*c^2/81 - 19*a*b^2*c^3/81 - 2*a*b*c^4/27 + 2*a*c^5/81 + 2*b^6/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 16*b^3*c^3/81 + 8*b^2*c^4/81 + 2*b*c^5/81 + 2*c^6/81) := by
    linear_combination (-2*a^5/81 - 2*a^4/27 - 8*a^3*b^2/81 + 2*a^3*b*c/27 + 2*a^3*b/27 - 8*a^3*c^2/81 + 2*a^3*c/27 + 7*a^3/9 - 8*a^2*b^3/81 + 7*a^2*b^2*c/27 + 17*a^2*b^2/27 + 7*a^2*b*c^2/27 + 2*a^2*b*c/27 + 4*a^2*b/9 - 8*a^2*c^3/81 + 17*a^2*c^2/27 + 4*a^2*c/9 + a^2/3 + 2*a*b^3*c/27 + 2*a*b^3/27 + 7*a*b^2*c^2/27 + 2*a*b^2*c/27 + 4*a*b^2/9 + 2*a*b*c^3/27 + 2*a*b*c^2/27 + a*b*c/3 + a*b + 2*a*c^3/27 + 4*a*c^2/9 + a*c - 2*b^5/81 - 2*b^4/27 - 8*b^3*c^2/81 + 2*b^3*c/27 + 7*b^3/9 - 8*b^2*c^3/81 + 17*b^2*c^2/27 + 4*b^2*c/9 + b^2/3 + 2*b*c^3/27 + 4*b*c^2/9 + b*c - 2*c^5/81 - 2*c^4/27 + 7*c^3/9 + c^2/3) * habc
  have hn : 0 ≤ (a^4 + a^3*b^2 + a^3*b + a^3*c^2 + a^3*c - 2*a^3 + a^2*b^3 + a^2*b^2*c^2 - a^2*b^2 + a^2*b*c + a^2*c^3 - a^2*c^2 - a^2 + a*b^3 + a*b^2*c + a*b*c^2 + 2*a*b*c - 3*a*b + a*c^3 - 3*a*c + b^4 + b^3*c^2 + b^3*c - 2*b^3 + b^2*c^3 - b^2*c^2 - b^2 + b*c^3 - 3*b*c + c^4 - 2*c^3 - c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (a ^ 2 + b + c) + 1 / (b ^ 2 + a + c) + 1 / (c ^ 2 + a + b) ≤ 1) := @solution
#print axioms solution
