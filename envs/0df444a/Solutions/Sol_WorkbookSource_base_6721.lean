-- Prove2me | solution 1 for WorkbookSource.base_6721
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:55.577964+00:00
-- url     : https://prove2.me/submissions/3dad391a-6013-46bf-b640-77a23b14edb0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : (a^3 - 8 * a + 8) / (b + c) + (b^3 - 8 * b + 8) / (c + a) + (c^3 - 8 * c + 8) / (a + b) ≥ 3 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (22*a^5/27 - a^4*b/9 - a^4*c/9 - 11*a^3*b^2/27 - 11*a^3*c^2/27 - 11*a^2*b^3/27 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 - 11*a^2*c^3/27 - a*b^4/9 + 2*a*b^2*c^2/9 - a*c^4/9 + 22*b^5/27 - b^4*c/9 - 11*b^3*c^2/27 - 11*b^2*c^3/27 - b*c^4/9 + 22*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (b - a)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^3 * (c - b)^2 + (50/9 : ℝ) * a^2 * (b - a)^3 + (25/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (47/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (58/9 : ℝ) * a^2 * (c - b)^3 + (80/27 : ℝ) * a^1 * (b - a)^4 + (160/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (154/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (382/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (104/27 : ℝ) * a^1 * (c - b)^4 + (16/27 : ℝ) * (b - a)^5 + (40/27 : ℝ) * (b - a)^4 * (c - b)^1 + (158/27 : ℝ) * (b - a)^3 * (c - b)^2 + (197/27 : ℝ) * (b - a)^2 * (c - b)^3 + (107/27 : ℝ) * (b - a)^1 * (c - b)^4 + (22/27 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (22*a^5/27 - a^4*b/9 - a^4*c/9 - 11*a^3*b^2/27 - 11*a^3*c^2/27 - 11*a^2*b^3/27 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 - 11*a^2*c^3/27 - a*b^4/9 + 2*a*b^2*c^2/9 - a*c^4/9 + 22*b^5/27 - b^4*c/9 - 11*b^3*c^2/27 - 11*b^2*c^3/27 - b*c^4/9 + 22*c^5/27) := by
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
  have he : (2*a^5 + 2*a^4*b + 2*a^4*c + 2*a^3*b*c - 16*a^3 - 19*a^2*b - 19*a^2*c + 16*a^2 + 2*a*b^4 + 2*a*b^3*c - 19*a*b^2 + 2*a*b*c^3 - 54*a*b*c + 48*a*b + 2*a*c^4 - 19*a*c^2 + 48*a*c + 2*b^5 + 2*b^4*c - 16*b^3 - 19*b^2*c + 16*b^2 + 2*b*c^4 - 19*b*c^2 + 48*b*c + 2*c^5 - 16*c^3 + 16*c^2) = (22*a^5/27 - a^4*b/9 - a^4*c/9 - 11*a^3*b^2/27 - 11*a^3*c^2/27 - 11*a^2*b^3/27 + 2*a^2*b^2*c/9 + 2*a^2*b*c^2/9 - 11*a^2*c^3/27 - a*b^4/9 + 2*a*b^2*c^2/9 - a*c^4/9 + 22*b^5/27 - b^4*c/9 - 11*b^3*c^2/27 - 11*b^2*c^3/27 - b*c^4/9 + 22*c^5/27) := by
    linear_combination (32*a^4/27 + 25*a^3*b/27 + 25*a^3*c/27 + 32*a^3/9 - 14*a^2*b^2/27 + 4*a^2*b*c/27 - 7*a^2*b/9 - 14*a^2*c^2/27 - 7*a^2*c/9 - 16*a^2/3 + 25*a*b^3/27 + 4*a*b^2*c/27 - 7*a*b^2/9 + 4*a*b*c^2/27 + 2*a*b*c - 16*a*b + 25*a*c^3/27 - 7*a*c^2/9 - 16*a*c + 32*b^4/27 + 25*b^3*c/27 + 32*b^3/9 - 14*b^2*c^2/27 - 7*b^2*c/9 - 16*b^2/3 + 25*b*c^3/27 - 7*b*c^2/9 - 16*b*c + 32*c^4/27 + 32*c^3/9 - 16*c^2/3) * habc
  have hn : 0 ≤ (2*a^5 + 2*a^4*b + 2*a^4*c + 2*a^3*b*c - 16*a^3 - 19*a^2*b - 19*a^2*c + 16*a^2 + 2*a*b^4 + 2*a*b^3*c - 19*a*b^2 + 2*a*b*c^3 - 54*a*b*c + 48*a*b + 2*a*c^4 - 19*a*c^2 + 48*a*c + 2*b^5 + 2*b^4*c - 16*b^3 - 19*b^2*c + 16*b^2 + 2*b*c^4 - 19*b*c^2 + 48*b*c + 2*c^5 - 16*c^3 + 16*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), (a^3 - 8 * a + 8) / (b + c) + (b^3 - 8 * b + 8) / (c + a) + (c^3 - 8 * c + 8) / (a + b) ≥ 3 / 2) := @solution
#print axioms solution
