-- Prove2me | solution 1 for WorkbookSource.base_6003
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:43.337434+00:00
-- url     : https://prove2.me/submissions/498d0522-0e87-43bf-b0e1-14563a140a42

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (b ^ 2 + c) + b / (c ^ 2 + a) + c / (a ^ 2 + b) ≥ 3 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6/9 + 14*a^5*b/27 + a^5*c/9 - 5*a^4*b^2/9 + a^4*b*c/9 + 8*a^4*c^2/27 - 4*a^3*b^3/9 - 13*a^3*b^2*c/27 + 7*a^3*b*c^2/9 - 4*a^3*c^3/9 + 8*a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/3 - 13*a^2*b*c^3/27 - 5*a^2*c^4/9 + a*b^5/9 + a*b^4*c/9 - 13*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + a*b*c^4/9 + 14*a*c^5/27 + 2*b^6/9 + 14*b^5*c/27 - 5*b^4*c^2/9 - 4*b^3*c^3/9 + 8*b^2*c^4/27 + b*c^5/9 + 2*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (106/9 : ℝ) * a^3 * (b - a)^3 + (59/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (27 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (86/9 : ℝ) * a^3 * (c - b)^3 + (29/3 : ℝ) * a^2 * (b - a)^4 + (70/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (128/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (29 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (19/3 : ℝ) * a^2 * (c - b)^4 + (91/27 : ℝ) * a^1 * (b - a)^5 + (277/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (676/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (683/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (299/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (53/27 : ℝ) * a^1 * (c - b)^5 + (10/27 : ℝ) * (b - a)^6 + (31/27 : ℝ) * (b - a)^5 * (c - b)^1 + (13/3 : ℝ) * (b - a)^4 * (c - b)^2 + (170/27 : ℝ) * (b - a)^3 * (c - b)^3 + (113/27 : ℝ) * (b - a)^2 * (c - b)^4 + (13/9 : ℝ) * (b - a)^1 * (c - b)^5 + (2/9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^6/9 + 14*a^5*b/27 + a^5*c/9 - 5*a^4*b^2/9 + a^4*b*c/9 + 8*a^4*c^2/27 - 4*a^3*b^3/9 - 13*a^3*b^2*c/27 + 7*a^3*b*c^2/9 - 4*a^3*c^3/9 + 8*a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/3 - 13*a^2*b*c^3/27 - 5*a^2*c^4/9 + a*b^5/9 + a*b^4*c/9 - 13*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + a*b*c^4/9 + 14*a*c^5/27 + 2*b^6/9 + 14*b^5*c/27 - 5*b^4*c^2/9 - 4*b^3*c^3/9 + 8*b^2*c^4/27 + b*c^5/9 + 2*c^6/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (c - a)^2 + (16/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16/3 : ℝ) * a^4 * (b - c)^2 + (106/9 : ℝ) * a^3 * (c - a)^3 + (47/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (23 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (86/9 : ℝ) * a^3 * (b - c)^3 + (29/3 : ℝ) * a^2 * (c - a)^4 + (46/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (92/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (25 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (19/3 : ℝ) * a^2 * (b - c)^4 + (91/27 : ℝ) * a^1 * (c - a)^5 + (178/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (478/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (593/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (308/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (53/27 : ℝ) * a^1 * (b - c)^5 + (10/27 : ℝ) * (c - a)^6 + (29/27 : ℝ) * (c - a)^5 * (b - c)^1 + (112/27 : ℝ) * (c - a)^4 * (b - c)^2 + (188/27 : ℝ) * (c - a)^3 * (b - c)^3 + (145/27 : ℝ) * (c - a)^2 * (b - c)^4 + (50/27 : ℝ) * (c - a)^1 * (b - c)^5 + (2/9 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6/9 + 14*a^5*b/27 + a^5*c/9 - 5*a^4*b^2/9 + a^4*b*c/9 + 8*a^4*c^2/27 - 4*a^3*b^3/9 - 13*a^3*b^2*c/27 + 7*a^3*b*c^2/9 - 4*a^3*c^3/9 + 8*a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/3 - 13*a^2*b*c^3/27 - 5*a^2*c^4/9 + a*b^5/9 + a*b^4*c/9 - 13*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + a*b*c^4/9 + 14*a*c^5/27 + 2*b^6/9 + 14*b^5*c/27 - 5*b^4*c^2/9 - 4*b^3*c^3/9 + 8*b^2*c^4/27 + b*c^5/9 + 2*c^6/9) := by
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
  have he : (2*a^4 - 3*a^3*b^2 + 2*a^3*c^2 - 3*a^3*c + 2*a^2*b^3 - 3*a^2*b^2*c^2 + 2*a^2*b*c + 2*a^2*b - 3*a^2*c^3 - 3*a*b^3 + 2*a*b^2*c + 2*a*b*c^2 - 3*a*b*c + 2*a*c^2 + 2*b^4 - 3*b^3*c^2 + 2*b^2*c^3 + 2*b^2*c - 3*b*c^3 + 2*c^4) = (2*a^6/9 + 14*a^5*b/27 + a^5*c/9 - 5*a^4*b^2/9 + a^4*b*c/9 + 8*a^4*c^2/27 - 4*a^3*b^3/9 - 13*a^3*b^2*c/27 + 7*a^3*b*c^2/9 - 4*a^3*c^3/9 + 8*a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/3 - 13*a^2*b*c^3/27 - 5*a^2*c^4/9 + a*b^5/9 + a*b^4*c/9 - 13*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + a*b*c^4/9 + 14*a*c^5/27 + 2*b^6/9 + 14*b^5*c/27 - 5*b^4*c^2/9 - 4*b^3*c^3/9 + 8*b^2*c^4/27 + b*c^5/9 + 2*c^6/9) := by
    linear_combination (-2*a^5/9 - 8*a^4*b/27 + a^4*c/9 - 2*a^4/3 + 23*a^3*b^2/27 + 2*a^3*b*c/27 - 2*a^3*b/9 - 11*a^3*c^2/27 + a^3*c - 11*a^2*b^3/27 - 4*a^2*b^2*c/9 - 2*a^2*b^2/9 - 4*a^2*b*c^2/9 - 5*a^2*b*c/9 - 2*a^2*b/3 + 23*a^2*c^3/27 - 2*a^2*c^2/9 + a*b^4/9 + 2*a*b^3*c/27 + a*b^3 - 4*a*b^2*c^2/9 - 5*a*b^2*c/9 + 2*a*b*c^3/27 - 5*a*b*c^2/9 + a*b*c - 8*a*c^4/27 - 2*a*c^3/9 - 2*a*c^2/3 - 2*b^5/9 - 8*b^4*c/27 - 2*b^4/3 + 23*b^3*c^2/27 - 2*b^3*c/9 - 11*b^2*c^3/27 - 2*b^2*c^2/9 - 2*b^2*c/3 + b*c^4/9 + b*c^3 - 2*c^5/9 - 2*c^4/3) * habc
  have hn : 0 ≤ (2*a^4 - 3*a^3*b^2 + 2*a^3*c^2 - 3*a^3*c + 2*a^2*b^3 - 3*a^2*b^2*c^2 + 2*a^2*b*c + 2*a^2*b - 3*a^2*c^3 - 3*a*b^3 + 2*a*b^2*c + 2*a*b*c^2 - 3*a*b*c + 2*a*c^2 + 2*b^4 - 3*b^3*c^2 + 2*b^2*c^3 + 2*b^2*c - 3*b*c^3 + 2*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (b ^ 2 + c) + b / (c ^ 2 + a) + c / (a ^ 2 + b) ≥ 3 / 2) := @solution
#print axioms solution
