-- Prove2me | solution 1 for WorkbookSource.base_17772
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:10:11.210389+00:00
-- url     : https://prove2.me/submissions/0e133097-7ebe-4d99-9bea-af48a7e85732

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b^3) / (c + 1) + (b + c^3) / (a + 1) + (c + a^3) / (b + 1) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5/9 + 14*a^4*b/27 + 47*a^4*c/27 - a^3*b^2/9 - 16*a^3*b*c/27 + a^3*c^2/9 + a^2*b^3/9 - 19*a^2*b^2*c/9 - 19*a^2*b*c^2/9 - a^2*c^3/9 + 47*a*b^4/27 - 16*a*b^3*c/27 - 19*a*b^2*c^2/9 - 16*a*b*c^3/27 + 14*a*c^4/27 + 4*b^5/9 + 14*b^4*c/27 - b^3*c^2/9 + b^2*c^3/9 + 47*b*c^4/27 + 4*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (b - a)^2 + (12 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^3 * (c - b)^2 + (208/9 : ℝ) * a^2 * (b - a)^3 + (116/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (124/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (116/9 : ℝ) * a^2 * (c - b)^3 + (397/27 : ℝ) * a^1 * (b - a)^4 + (938/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (401/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (662/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (121/27 : ℝ) * a^1 * (c - b)^4 + (85/27 : ℝ) * (b - a)^5 + (265/27 : ℝ) * (b - a)^4 * (c - b)^1 + (136/9 : ℝ) * (b - a)^3 * (c - b)^2 + (311/27 : ℝ) * (b - a)^2 * (c - b)^3 + (107/27 : ℝ) * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5/9 + 14*a^4*b/27 + 47*a^4*c/27 - a^3*b^2/9 - 16*a^3*b*c/27 + a^3*c^2/9 + a^2*b^3/9 - 19*a^2*b^2*c/9 - 19*a^2*b*c^2/9 - a^2*c^3/9 + 47*a*b^4/27 - 16*a*b^3*c/27 - 19*a*b^2*c^2/9 - 16*a*b*c^3/27 + 14*a*c^4/27 + 4*b^5/9 + 14*b^4*c/27 - b^3*c^2/9 + b^2*c^3/9 + 47*b*c^4/27 + 4*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (c - a)^2 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^3 * (b - c)^2 + (208/9 : ℝ) * a^2 * (c - a)^3 + (92/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (100/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (116/9 : ℝ) * a^2 * (b - c)^3 + (397/27 : ℝ) * a^1 * (c - a)^4 + (650/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (257/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (518/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (121/27 : ℝ) * a^1 * (b - c)^4 + (85/27 : ℝ) * (c - a)^5 + (160/27 : ℝ) * (c - a)^4 * (b - c)^1 + (22/3 : ℝ) * (c - a)^3 * (b - c)^2 + (173/27 : ℝ) * (c - a)^2 * (b - c)^3 + (74/27 : ℝ) * (c - a)^1 * (b - c)^4 + (4/9 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5/9 + 14*a^4*b/27 + 47*a^4*c/27 - a^3*b^2/9 - 16*a^3*b*c/27 + a^3*c^2/9 + a^2*b^3/9 - 19*a^2*b^2*c/9 - 19*a^2*b*c^2/9 - a^2*c^3/9 + 47*a*b^4/27 - 16*a*b^3*c/27 - 19*a*b^2*c^2/9 - 16*a*b*c^3/27 + 14*a*c^4/27 + 4*b^5/9 + 14*b^4*c/27 - b^3*c^2/9 + b^2*c^3/9 + 47*b*c^4/27 + 4*c^5/9) := by
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
  have he : (a^4*c + a^4 + a^3*c + a^3 + a^2*b + a^2 + a*b^4 + a*b^3 - 3*a*b*c - 2*a*b + a*c^2 - 2*a*c - 2*a + b^4 + b^3 + b^2*c + b^2 + b*c^4 + b*c^3 - 2*b*c - 2*b + c^4 + c^3 + c^2 - 2*c - 3) = (4*a^5/9 + 14*a^4*b/27 + 47*a^4*c/27 - a^3*b^2/9 - 16*a^3*b*c/27 + a^3*c^2/9 + a^2*b^3/9 - 19*a^2*b^2*c/9 - 19*a^2*b*c^2/9 - a^2*c^3/9 + 47*a*b^4/27 - 16*a*b^3*c/27 - 19*a*b^2*c^2/9 - 16*a*b*c^3/27 + 14*a*c^4/27 + 4*b^5/9 + 14*b^4*c/27 - b^3*c^2/9 + b^2*c^3/9 + 47*b*c^4/27 + 4*c^5/9) := by
    linear_combination (-4*a^4/9 - 2*a^3*b/27 - 8*a^3*c/27 - a^3/3 + 5*a^2*b^2/27 + 26*a^2*b*c/27 + a^2*b/9 + 5*a^2*c^2/27 + 4*a^2*c/9 - 8*a*b^3/27 + 26*a*b^2*c/27 + 4*a*b^2/9 + 26*a*b*c^2/27 + 7*a*b*c/3 + 4*a*b/3 - 2*a*c^3/27 + a*c^2/9 + 4*a*c/3 + a - 4*b^4/9 - 2*b^3*c/27 - b^3/3 + 5*b^2*c^2/27 + b^2*c/9 - 8*b*c^3/27 + 4*b*c^2/9 + 4*b*c/3 + b - 4*c^4/9 - c^3/3 + c + 1) * habc
  have hn : 0 ≤ (a^4*c + a^4 + a^3*c + a^3 + a^2*b + a^2 + a*b^4 + a*b^3 - 3*a*b*c - 2*a*b + a*c^2 - 2*a*c - 2*a + b^4 + b^3 + b^2*c + b^2 + b*c^4 + b*c^3 - 2*b*c - 2*b + c^4 + c^3 + c^2 - 2*c - 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a + b^3) / (c + 1) + (b + c^3) / (a + 1) + (c + a^3) / (b + 1) ≥ 3) := @solution
#print axioms solution
