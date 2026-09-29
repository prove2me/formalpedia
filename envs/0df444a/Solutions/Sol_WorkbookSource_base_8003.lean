-- Prove2me | solution 1 for WorkbookSource.base_8003
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:34:44.148626+00:00
-- url     : https://prove2.me/submissions/4536df50-be9c-4c5f-b790-44c92bc370ad

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) + (c^3 + 3 * a^3) / (5 * c + a) ≥ 2 * (a^2 + b^2 + c^2) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (190*a^4*b + 38*a^4*c + 35*a^3*b^2 - 168*a^3*b*c - 35*a^3*c^2 - 35*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 + 35*a^2*c^3 + 38*a*b^4 - 168*a*b^3*c - 60*a*b^2*c^2 - 168*a*b*c^3 + 190*a*c^4 + 190*b^4*c + 35*b^3*c^2 - 35*b^2*c^3 + 38*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (744 : ℝ) * a^3 * (b - a)^2 + (744 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (744 : ℝ) * a^3 * (c - b)^2 + (1488 : ℝ) * a^2 * (b - a)^3 + (1671 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1671 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (744 : ℝ) * a^2 * (c - b)^3 + (972 : ℝ) * a^1 * (b - a)^4 + (1196 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1050 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (826 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (228 : ℝ) * a^1 * (c - b)^4 + (228 : ℝ) * (b - a)^5 + (307 : ℝ) * (b - a)^4 * (c - b)^1 + (158 : ℝ) * (b - a)^3 * (c - b)^2 + (117 : ℝ) * (b - a)^2 * (c - b)^3 + (38 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (190*a^4*b + 38*a^4*c + 35*a^3*b^2 - 168*a^3*b*c - 35*a^3*c^2 - 35*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 + 35*a^2*c^3 + 38*a*b^4 - 168*a*b^3*c - 60*a*b^2*c^2 - 168*a*b*c^3 + 190*a*c^4 + 190*b^4*c + 35*b^3*c^2 - 35*b^2*c^3 + 38*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (744 : ℝ) * a^3 * (c - a)^2 + (744 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (744 : ℝ) * a^3 * (b - c)^2 + (1488 : ℝ) * a^2 * (c - a)^3 + (2793 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (2793 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (744 : ℝ) * a^2 * (b - c)^3 + (972 : ℝ) * a^1 * (c - a)^4 + (2692 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (3294 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (1574 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (228 : ℝ) * a^1 * (b - c)^4 + (228 : ℝ) * (c - a)^5 + (833 : ℝ) * (c - a)^4 * (b - c)^1 + (1210 : ℝ) * (c - a)^3 * (b - c)^2 + (795 : ℝ) * (c - a)^2 * (b - c)^3 + (190 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (190*a^4*b + 38*a^4*c + 35*a^3*b^2 - 168*a^3*b*c - 35*a^3*c^2 - 35*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 + 35*a^2*c^3 + 38*a*b^4 - 168*a*b^3*c - 60*a*b^2*c^2 - 168*a*b*c^3 + 190*a*c^4 + 190*b^4*c + 35*b^3*c^2 - 35*b^2*c^3 + 38*b*c^4) := by
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
  have hn : 0 ≤ (190*a^4*b + 38*a^4*c + 35*a^3*b^2 - 168*a^3*b*c - 35*a^3*c^2 - 35*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 + 35*a^2*c^3 + 38*a*b^4 - 168*a*b^3*c - 60*a*b^2*c^2 - 168*a*b*c^3 + 190*a*c^4 + 190*b^4*c + 35*b^3*c^2 - 35*b^2*c^3 + 38*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) + (c^3 + 3 * a^3) / (5 * c + a) ≥ 2 * (a^2 + b^2 + c^2) / 3) := @solution
#print axioms solution
