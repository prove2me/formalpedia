-- Prove2me | solution 1 for WorkbookSource.base_23288
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:55:11.020544+00:00
-- url     : https://prove2.me/submissions/822e741b-c3b0-4b0e-aa64-f6d213f7b156

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a^2 + b + c + 1) + 1 / (b^2 + c + a + 1) + 1 / (c^2 + a + b + 1) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (32*a^6/243 + 16*a^5*b/81 + 16*a^5*c/81 + 40*a^4*b^2/81 - 22*a^4*b*c/81 + 40*a^4*c^2/81 + 208*a^3*b^3/243 - 83*a^3*b^2*c/81 - 83*a^3*b*c^2/81 + 208*a^3*c^3/243 + 40*a^2*b^4/81 - 83*a^2*b^3*c/81 - 4*a^2*b^2*c^2/27 - 83*a^2*b*c^3/81 + 40*a^2*c^4/81 + 16*a*b^5/81 - 22*a*b^4*c/81 - 83*a*b^3*c^2/81 - 83*a*b^2*c^3/81 - 22*a*b*c^4/81 + 16*a*c^5/81 + 32*b^6/243 + 16*b^5*c/81 + 40*b^4*c^2/81 + 208*b^3*c^3/243 + 40*b^2*c^4/81 + 16*b*c^5/81 + 32*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (206/9 : ℝ) * a^3 * (b - a)^3 + (103/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (89/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (82/9 : ℝ) * a^3 * (c - b)^3 + (76/3 : ℝ) * a^2 * (b - a)^4 + (152/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (145/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (23 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14/3 : ℝ) * a^2 * (c - b)^4 + (346/27 : ℝ) * a^1 * (b - a)^5 + (865/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (976/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (599/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (206/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (32/27 : ℝ) * a^1 * (c - b)^5 + (608/243 : ℝ) * (b - a)^6 + (608/81 : ℝ) * (b - a)^5 * (c - b)^1 + (808/81 : ℝ) * (b - a)^4 * (c - b)^2 + (1808/243 : ℝ) * (b - a)^3 * (c - b)^3 + (280/81 : ℝ) * (b - a)^2 * (c - b)^4 + (80/81 : ℝ) * (b - a)^1 * (c - b)^5 + (32/243 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (32*a^6/243 + 16*a^5*b/81 + 16*a^5*c/81 + 40*a^4*b^2/81 - 22*a^4*b*c/81 + 40*a^4*c^2/81 + 208*a^3*b^3/243 - 83*a^3*b^2*c/81 - 83*a^3*b*c^2/81 + 208*a^3*c^3/243 + 40*a^2*b^4/81 - 83*a^2*b^3*c/81 - 4*a^2*b^2*c^2/27 - 83*a^2*b*c^3/81 + 40*a^2*c^4/81 + 16*a*b^5/81 - 22*a*b^4*c/81 - 83*a*b^3*c^2/81 - 83*a*b^2*c^3/81 - 22*a*b*c^4/81 + 16*a*c^5/81 + 32*b^6/243 + 16*b^5*c/81 + 40*b^4*c^2/81 + 208*b^3*c^3/243 + 40*b^2*c^4/81 + 16*b*c^5/81 + 32*c^6/243) := by
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
  have he : (3*a^4 + 3*a^3*b^2 + 3*a^3*b + 3*a^3*c^2 + 3*a^3*c - 2*a^3 + 3*a^2*b^3 + 3*a^2*b^2*c^2 - a^2*b^2 + 3*a^2*b*c + 2*a^2*b + 3*a^2*c^3 - a^2*c^2 + 2*a^2*c - 6*a^2 + 3*a*b^3 + 3*a*b^2*c + 2*a*b^2 + 3*a*b*c^2 + 6*a*b*c - 3*a*b + 3*a*c^3 + 2*a*c^2 - 3*a*c - 10*a + 3*b^4 + 3*b^3*c^2 + 3*b^3*c - 2*b^3 + 3*b^2*c^3 - b^2*c^2 + 2*b^2*c - 6*b^2 + 3*b*c^3 + 2*b*c^2 - 3*b*c - 10*b + 3*c^4 - 2*c^3 - 6*c^2 - 10*c - 9) = (32*a^6/243 + 16*a^5*b/81 + 16*a^5*c/81 + 40*a^4*b^2/81 - 22*a^4*b*c/81 + 40*a^4*c^2/81 + 208*a^3*b^3/243 - 83*a^3*b^2*c/81 - 83*a^3*b*c^2/81 + 208*a^3*c^3/243 + 40*a^2*b^4/81 - 83*a^2*b^3*c/81 - 4*a^2*b^2*c^2/27 - 83*a^2*b*c^3/81 + 40*a^2*c^4/81 + 16*a*b^5/81 - 22*a*b^4*c/81 - 83*a*b^3*c^2/81 - 83*a*b^2*c^3/81 - 22*a*b*c^4/81 + 16*a*c^5/81 + 32*b^6/243 + 16*b^5*c/81 + 40*b^4*c^2/81 + 208*b^3*c^3/243 + 40*b^2*c^4/81 + 16*b*c^5/81 + 32*c^6/243) := by
    linear_combination (-32*a^5/243 - 16*a^4*b/243 - 16*a^4*c/243 - 32*a^4/81 - 104*a^3*b^2/243 + 98*a^3*b*c/243 + 16*a^3*b/81 - 104*a^3*c^2/243 + 16*a^3*c/81 + 49*a^3/27 - 104*a^2*b^3/243 + 85*a^2*b^2*c/81 + 41*a^2*b^2/27 + 85*a^2*b*c^2/81 + 22*a^2*b*c/27 + 16*a^2*b/9 - 104*a^2*c^3/243 + 41*a^2*c^2/27 + 16*a^2*c/9 + 31*a^2/9 - 16*a*b^4/243 + 98*a*b^3*c/243 + 16*a*b^3/81 + 85*a*b^2*c^2/81 + 22*a*b^2*c/27 + 16*a*b^2/9 + 98*a*b*c^3/243 + 22*a*b*c^2/27 + 17*a*b*c/9 + 35*a*b/9 - 16*a*c^4/243 + 16*a*c^3/81 + 16*a*c^2/9 + 35*a*c/9 + 13*a/3 - 32*b^5/243 - 16*b^4*c/243 - 32*b^4/81 - 104*b^3*c^2/243 + 16*b^3*c/81 + 49*b^3/27 - 104*b^2*c^3/243 + 41*b^2*c^2/27 + 16*b^2*c/9 + 31*b^2/9 - 16*b*c^4/243 + 16*b*c^3/81 + 16*b*c^2/9 + 35*b*c/9 + 13*b/3 - 32*c^5/243 - 32*c^4/81 + 49*c^3/27 + 31*c^2/9 + 13*c/3 + 3) * habc
  have hn : 0 ≤ (3*a^4 + 3*a^3*b^2 + 3*a^3*b + 3*a^3*c^2 + 3*a^3*c - 2*a^3 + 3*a^2*b^3 + 3*a^2*b^2*c^2 - a^2*b^2 + 3*a^2*b*c + 2*a^2*b + 3*a^2*c^3 - a^2*c^2 + 2*a^2*c - 6*a^2 + 3*a*b^3 + 3*a*b^2*c + 2*a*b^2 + 3*a*b*c^2 + 6*a*b*c - 3*a*b + 3*a*c^3 + 2*a*c^2 - 3*a*c - 10*a + 3*b^4 + 3*b^3*c^2 + 3*b^3*c - 2*b^3 + 3*b^2*c^3 - b^2*c^2 + 2*b^2*c - 6*b^2 + 3*b*c^3 + 2*b*c^2 - 3*b*c - 10*b + 3*c^4 - 2*c^3 - 6*c^2 - 10*c - 9) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (a^2 + b + c + 1) + 1 / (b^2 + c + a + 1) + 1 / (c^2 + a + b + 1) ≤ 3 / 4) := @solution
#print axioms solution
