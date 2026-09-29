-- Prove2me | solution 1 for WorkbookSource.base_4484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:29:38.606782+00:00
-- url     : https://prove2.me/submissions/7556c2ad-8cfb-4f1d-aef7-2515d687ba23

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c) ^ 2 ≥ 1 / a ^ 2 + 4 / (b ^ 2 + c ^ 2) + 18 / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^5 * (b - a)^2 + (20 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^5 * (c - b)^2 + (96 : ℝ) * a^4 * (b - a)^3 + (144 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (176 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^4 * (c - b)^3 + (184 : ℝ) * a^3 * (b - a)^4 + (368 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (434 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (250 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (53 : ℝ) * a^3 * (c - b)^4 + (176 : ℝ) * a^2 * (b - a)^5 + (440 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (556 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (394 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (146 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (22 : ℝ) * a^2 * (c - b)^5 + (84 : ℝ) * a^1 * (b - a)^6 + (252 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (354 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (288 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (138 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (36 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^1 * (c - b)^6 + (16 : ℝ) * (b - a)^7 + (56 : ℝ) * (b - a)^6 * (c - b)^1 + (88 : ℝ) * (b - a)^5 * (c - b)^2 + (80 : ℝ) * (b - a)^4 * (c - b)^3 + (44 : ℝ) * (b - a)^3 * (c - b)^4 + (14 : ℝ) * (b - a)^2 * (c - b)^5 + (2 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * b^5 * (a - b)^2 + (44 : ℝ) * b^5 * (a - b)^1 * (c - a)^1 + (32 : ℝ) * b^5 * (c - a)^2 + (96 : ℝ) * b^4 * (a - b)^3 + (204 : ℝ) * b^4 * (a - b)^2 * (c - a)^1 + (176 : ℝ) * b^4 * (a - b)^1 * (c - a)^2 + (64 : ℝ) * b^4 * (c - a)^3 + (117 : ℝ) * b^3 * (a - b)^4 + (338 : ℝ) * b^3 * (a - b)^3 * (c - a)^1 + (386 : ℝ) * b^3 * (a - b)^2 * (c - a)^2 + (218 : ℝ) * b^3 * (a - b)^1 * (c - a)^3 + (53 : ℝ) * b^3 * (c - a)^4 + (73 : ℝ) * b^2 * (a - b)^5 + (266 : ℝ) * b^2 * (a - b)^4 * (c - a)^1 + (392 : ℝ) * b^2 * (a - b)^3 * (c - a)^2 + (300 : ℝ) * b^2 * (a - b)^2 * (c - a)^3 + (123 : ℝ) * b^2 * (a - b)^1 * (c - a)^4 + (22 : ℝ) * b^2 * (c - a)^5 + (22 : ℝ) * b^1 * (a - b)^6 + (96 : ℝ) * b^1 * (a - b)^5 * (c - a)^1 + (173 : ℝ) * b^1 * (a - b)^4 * (c - a)^2 + (166 : ℝ) * b^1 * (a - b)^3 * (c - a)^3 + (90 : ℝ) * b^1 * (a - b)^2 * (c - a)^4 + (26 : ℝ) * b^1 * (a - b)^1 * (c - a)^5 + (3 : ℝ) * b^1 * (c - a)^6 + (2 : ℝ) * (a - b)^7 + (10 : ℝ) * (a - b)^6 * (c - a)^1 + (21 : ℝ) * (a - b)^5 * (c - a)^2 + (24 : ℝ) * (a - b)^4 * (c - a)^3 + (16 : ℝ) * (a - b)^3 * (c - a)^4 + (6 : ℝ) * (a - b)^2 * (c - a)^5 + (1 : ℝ) * (a - b)^1 * (c - a)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * b^5 * (c - b)^2 + (20 : ℝ) * b^5 * (c - b)^1 * (a - c)^1 + (20 : ℝ) * b^5 * (a - c)^2 + (96 : ℝ) * b^4 * (c - b)^3 + (84 : ℝ) * b^4 * (c - b)^2 * (a - c)^1 + (56 : ℝ) * b^4 * (c - b)^1 * (a - c)^2 + (4 : ℝ) * b^4 * (a - c)^3 + (117 : ℝ) * b^3 * (c - b)^4 + (130 : ℝ) * b^3 * (c - b)^3 * (a - c)^1 + (74 : ℝ) * b^3 * (c - b)^2 * (a - c)^2 + (8 : ℝ) * b^3 * (c - b)^1 * (a - c)^3 + (73 : ℝ) * b^2 * (c - b)^5 + (99 : ℝ) * b^2 * (c - b)^4 * (a - c)^1 + (58 : ℝ) * b^2 * (c - b)^3 * (a - c)^2 + (10 : ℝ) * b^2 * (c - b)^2 * (a - c)^3 + (22 : ℝ) * b^1 * (c - b)^6 + (36 : ℝ) * b^1 * (c - b)^5 * (a - c)^1 + (23 : ℝ) * b^1 * (c - b)^4 * (a - c)^2 + (6 : ℝ) * b^1 * (c - b)^3 * (a - c)^3 + (2 : ℝ) * (c - b)^7 + (4 : ℝ) * (c - b)^6 * (a - c)^1 + (3 : ℝ) * (c - b)^5 * (a - c)^2 + (1 : ℝ) * (c - b)^4 * (a - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) := by nlinarith only [hp]
  have hd : 0 < (a*b^2*c^2*(b^2 + c^2)*(a^2 + b^2 + c^2)) := by positivity
  have heqrat : ( (1 / a + 1 / b + 1 / c) ^ 2 ) - ( 1 / a ^ 2 + 4 / (b ^ 2 + c ^ 2) + 18 / (a ^ 2 + b ^ 2 + c ^ 2)  ) = (a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 + 2*a^2*b*c^4 + a*b^6 + 2*a*b^5*c - 19*a*b^4*c^2 + 4*a*b^3*c^3 - 19*a*b^2*c^4 + 2*a*b*c^5 + a*c^6 + 2*b^6*c + 2*b^5*c^2 + 4*b^4*c^3 + 4*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6) / (a*b^2*c^2*(b^2 + c^2)*(a^2 + b^2 + c^2)) := by
    field_simp
    <;> ring
  have hzpos := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hzpos]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (1 / a + 1 / b + 1 / c) ^ 2 ≥ 1 / a ^ 2 + 4 / (b ^ 2 + c ^ 2) + 18 / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
