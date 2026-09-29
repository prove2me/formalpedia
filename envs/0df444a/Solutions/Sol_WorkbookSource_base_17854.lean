-- Prove2me | solution 1 for WorkbookSource.base_17854
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:10:12.548945+00:00
-- url     : https://prove2.me/submissions/7e210c6b-b129-4a01-a59b-dc32ef193430

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c + 3 / 2 * a * b * c ≥ 9 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - a^4*b*c/9 + 8*a^4*c^2/81 + 4*a^3*b^3/27 - 37*a^3*b^2*c/81 - 37*a^3*b*c^2/81 + 4*a^3*c^3/27 + 8*a^2*b^4/81 - 37*a^2*b^3*c/81 + 17*a^2*b^2*c^2/9 - 37*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - a*b^4*c/9 - 37*a*b^3*c^2/81 - 37*a*b^2*c^3/81 - a*b*c^4/9 + 2*a*c^5/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 4*b^3*c^3/27 + 8*b^2*c^4/81 + 2*b*c^5/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * a^4 * (b - a)^2 + (1/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1/3 : ℝ) * a^4 * (c - b)^2 + (10/9 : ℝ) * a^3 * (b - a)^3 + (5/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (2/9 : ℝ) * a^3 * (c - b)^3 + (5/3 : ℝ) * a^2 * (b - a)^4 + (10/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (8/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1/3 : ℝ) * a^2 * (c - b)^4 + (104/81 : ℝ) * a^1 * (b - a)^5 + (260/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (266/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (139/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (37/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/81 : ℝ) * a^1 * (c - b)^5 + (32/81 : ℝ) * (b - a)^6 + (32/27 : ℝ) * (b - a)^5 * (c - b)^1 + (112/81 : ℝ) * (b - a)^4 * (c - b)^2 + (64/81 : ℝ) * (b - a)^3 * (c - b)^3 + (2/9 : ℝ) * (b - a)^2 * (c - b)^4 + (2/81 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - a^4*b*c/9 + 8*a^4*c^2/81 + 4*a^3*b^3/27 - 37*a^3*b^2*c/81 - 37*a^3*b*c^2/81 + 4*a^3*c^3/27 + 8*a^2*b^4/81 - 37*a^2*b^3*c/81 + 17*a^2*b^2*c^2/9 - 37*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - a*b^4*c/9 - 37*a*b^3*c^2/81 - 37*a*b^2*c^3/81 - a*b*c^4/9 + 2*a*c^5/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 4*b^3*c^3/27 + 8*b^2*c^4/81 + 2*b*c^5/81) := by
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
  have he : (3*a^2*b^2*c^2 - 9*a*b*c + 2*a*b + 2*a*c + 2*b*c) = (2*a^5*b/81 + 2*a^5*c/81 + 8*a^4*b^2/81 - a^4*b*c/9 + 8*a^4*c^2/81 + 4*a^3*b^3/27 - 37*a^3*b^2*c/81 - 37*a^3*b*c^2/81 + 4*a^3*c^3/27 + 8*a^2*b^4/81 - 37*a^2*b^3*c/81 + 17*a^2*b^2*c^2/9 - 37*a^2*b*c^3/81 + 8*a^2*c^4/81 + 2*a*b^5/81 - a*b^4*c/9 - 37*a*b^3*c^2/81 - 37*a*b^2*c^3/81 - a*b*c^4/9 + 2*a*c^5/81 + 2*b^5*c/81 + 8*b^4*c^2/81 + 4*b^3*c^3/27 + 8*b^2*c^4/81 + 2*b*c^5/81) := by
    linear_combination (-2*a^4*b/81 - 2*a^4*c/81 - 2*a^3*b^2/27 + 13*a^3*b*c/81 - 2*a^3*b/27 - 2*a^3*c^2/27 - 2*a^3*c/27 - 2*a^2*b^3/27 + 10*a^2*b^2*c/27 - 4*a^2*b^2/27 + 10*a^2*b*c^2/27 + 17*a^2*b*c/27 - 2*a^2*b/9 - 2*a^2*c^3/27 - 4*a^2*c^2/27 - 2*a^2*c/9 - 2*a*b^4/81 + 13*a*b^3*c/81 - 2*a*b^3/27 + 10*a*b^2*c^2/27 + 17*a*b^2*c/27 - 2*a*b^2/9 + 13*a*b*c^3/81 + 17*a*b*c^2/27 + 7*a*b*c/3 - 2*a*b/3 - 2*a*c^4/81 - 2*a*c^3/27 - 2*a*c^2/9 - 2*a*c/3 - 2*b^4*c/81 - 2*b^3*c^2/27 - 2*b^3*c/27 - 2*b^2*c^3/27 - 4*b^2*c^2/27 - 2*b^2*c/9 - 2*b*c^4/81 - 2*b*c^3/27 - 2*b*c^2/9 - 2*b*c/3) * habc
  have hn : 0 ≤ (3*a^2*b^2*c^2 - 9*a*b*c + 2*a*b + 2*a*c + 2*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), 1 / a + 1 / b + 1 / c + 3 / 2 * a * b * c ≥ 9 / 2) := @solution
#print axioms solution
