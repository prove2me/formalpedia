-- Prove2me | solution 1 for WorkbookSource.base_17901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:10:13.584787+00:00
-- url     : https://prove2.me/submissions/c506e07e-9fab-46d3-a779-5ec5688ed109

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * (a + b - 2 * c) / (a * b + 3) + b * (b + c - 2 * a) / (b * c + 3) + c * (c + a - 2 * b) / (c * a + 3)) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/9 + a^5*b/3 + 2*a^5*c/3 - a^4*b^2/3 + 4*a^4*b*c/3 + a^4*c^2/3 - 7*a^3*b^3/9 - 8*a^3*b^2*c/3 + 2*a^3*b*c^2/3 - 7*a^3*c^3/9 + a^2*b^4/3 + 2*a^2*b^3*c/3 + a^2*b^2*c^2 - 8*a^2*b*c^3/3 - a^2*c^4/3 + 2*a*b^5/3 + 4*a*b^4*c/3 - 8*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 4*a*b*c^4/3 + a*c^5/3 + b^6/9 + b^5*c/3 - b^4*c^2/3 - 7*b^3*c^3/9 + b^2*c^4/3 + 2*b*c^5/3 + c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (18 : ℝ) * a^3 * (b - a)^3 + (33 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (43 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^3 * (c - b)^3 + (14 : ℝ) * a^2 * (b - a)^4 + (40 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (69 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (43 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^2 * (c - b)^4 + (13/3 : ℝ) * a^1 * (b - a)^5 + (55/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (124/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (113/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (41/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (5/3 : ℝ) * a^1 * (c - b)^5 + (4/9 : ℝ) * (b - a)^6 + (8/3 : ℝ) * (b - a)^5 * (c - b)^1 + (23/3 : ℝ) * (b - a)^4 * (c - b)^2 + (85/9 : ℝ) * (b - a)^3 * (c - b)^3 + (16/3 : ℝ) * (b - a)^2 * (c - b)^4 + (4/3 : ℝ) * (b - a)^1 * (c - b)^5 + (1/9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6/9 + a^5*b/3 + 2*a^5*c/3 - a^4*b^2/3 + 4*a^4*b*c/3 + a^4*c^2/3 - 7*a^3*b^3/9 - 8*a^3*b^2*c/3 + 2*a^3*b*c^2/3 - 7*a^3*c^3/9 + a^2*b^4/3 + 2*a^2*b^3*c/3 + a^2*b^2*c^2 - 8*a^2*b*c^3/3 - a^2*c^4/3 + 2*a*b^5/3 + 4*a*b^4*c/3 - 8*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 4*a*b*c^4/3 + a*c^5/3 + b^6/9 + b^5*c/3 - b^4*c^2/3 - 7*b^3*c^3/9 + b^2*c^4/3 + 2*b*c^5/3 + c^6/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (c - a)^2 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^4 * (b - c)^2 + (18 : ℝ) * a^3 * (c - a)^3 + (21 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (31 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (14 : ℝ) * a^3 * (b - c)^3 + (14 : ℝ) * a^2 * (c - a)^4 + (16 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (33 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (31 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (8 : ℝ) * a^2 * (b - c)^4 + (13/3 : ℝ) * a^1 * (c - a)^5 + (10/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (34/3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (59/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (32/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (5/3 : ℝ) * a^1 * (b - c)^5 + (4/9 : ℝ) * (c - a)^6 + (1 : ℝ) * (c - a)^4 * (b - c)^2 + (31/9 : ℝ) * (c - a)^3 * (b - c)^3 + (3 : ℝ) * (c - a)^2 * (b - c)^4 + (1 : ℝ) * (c - a)^1 * (b - c)^5 + (1/9 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/9 + a^5*b/3 + 2*a^5*c/3 - a^4*b^2/3 + 4*a^4*b*c/3 + a^4*c^2/3 - 7*a^3*b^3/9 - 8*a^3*b^2*c/3 + 2*a^3*b*c^2/3 - 7*a^3*c^3/9 + a^2*b^4/3 + 2*a^2*b^3*c/3 + a^2*b^2*c^2 - 8*a^2*b*c^3/3 - a^2*c^4/3 + 2*a*b^5/3 + 4*a*b^4*c/3 - 8*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 4*a*b*c^4/3 + a*c^5/3 + b^6/9 + b^5*c/3 - b^4*c^2/3 - 7*b^3*c^3/9 + b^2*c^4/3 + 2*b*c^5/3 + c^6/9) := by
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
  have he : (-2*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c + a^2*b^3*c + 3*a^2*b^2*c^2 - 6*a^2*b^2 - 2*a^2*b*c^3 + 3*a^2*b*c - 6*a^2*c^2 + 9*a^2 - 2*a*b^3*c^2 + 3*a*b^3 + a*b^2*c^3 + 3*a*b^2*c + 3*a*b*c^2 - 9*a*b - 9*a*c - 6*b^2*c^2 + 9*b^2 + 3*b*c^3 - 9*b*c + 9*c^2) = (a^6/9 + a^5*b/3 + 2*a^5*c/3 - a^4*b^2/3 + 4*a^4*b*c/3 + a^4*c^2/3 - 7*a^3*b^3/9 - 8*a^3*b^2*c/3 + 2*a^3*b*c^2/3 - 7*a^3*c^3/9 + a^2*b^4/3 + 2*a^2*b^3*c/3 + a^2*b^2*c^2 - 8*a^2*b*c^3/3 - a^2*c^4/3 + 2*a*b^5/3 + 4*a*b^4*c/3 - 8*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 4*a*b*c^4/3 + a*c^5/3 + b^6/9 + b^5*c/3 - b^4*c^2/3 - 7*b^3*c^3/9 + b^2*c^4/3 + 2*b*c^5/3 + c^6/9) := by
    linear_combination (-a^5/9 - 2*a^4*b/9 - 5*a^4*c/9 - a^4/3 + 5*a^3*b^2/9 - 5*a^3*b*c/9 - a^3*b/3 + 2*a^3*c^2/9 - 4*a^3*c/3 - a^3 + 2*a^2*b^3/9 + 2*a^2*b^2*c/3 + 2*a^2*b^2 + 2*a^2*b*c^2/3 + 5*a^2*c^3/9 + 2*a^2*c^2 - 3*a^2 - 5*a*b^4/9 - 5*a*b^3*c/9 - 4*a*b^3/3 + 2*a*b^2*c^2/3 - 5*a*b*c^3/9 + 3*a*b*c + 3*a*b - 2*a*c^4/9 - a*c^3/3 + 3*a*c - b^5/9 - 2*b^4*c/9 - b^4/3 + 5*b^3*c^2/9 - b^3*c/3 - b^3 + 2*b^2*c^3/9 + 2*b^2*c^2 - 3*b^2 - 5*b*c^4/9 - 4*b*c^3/3 + 3*b*c - c^5/9 - c^4/3 - c^3 - 3*c^2) * hab
  have hn : 0 ≤ (-2*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c + a^2*b^3*c + 3*a^2*b^2*c^2 - 6*a^2*b^2 - 2*a^2*b*c^3 + 3*a^2*b*c - 6*a^2*c^2 + 9*a^2 - 2*a*b^3*c^2 + 3*a*b^3 + a*b^2*c^3 + 3*a*b^2*c + 3*a*b*c^2 - 9*a*b - 9*a*c - 6*b^2*c^2 + 9*b^2 + 3*b*c^3 - 9*b*c + 9*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a * (a + b - 2 * c) / (a * b + 3) + b * (b + c - 2 * a) / (b * c + 3) + c * (c + a - 2 * b) / (c * a + 3)) ≥ 0) := @solution
#print axioms solution
