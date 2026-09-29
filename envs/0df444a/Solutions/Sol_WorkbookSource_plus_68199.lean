-- Prove2me | solution 1 for WorkbookSource.plus_68199
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:14.60146+00:00
-- url     : https://prove2.me/submissions/d1b6e3f4-c242-4c4c-9446-870ab29c02bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * a ^ 6 + 20 * a ^ 5 * b + 17 * a ^ 4 * b ^ 2 + 10 * a ^ 3 * b ^ 3 + 17 * a ^ 2 * b ^ 4 + 20 * a * b ^ 5 + 8 * b ^ 6 + 20 * a ^ 5 * c + 18 * a ^ 4 * b * c - 38 * a ^ 3 * b ^ 2 * c - 38 * a ^ 2 * b ^ 3 * c + 18 * a * b ^ 4 * c + 20 * b ^ 5 * c + 17 * a ^ 4 * c ^ 2 - 38 * a ^ 3 * b * c ^ 2 - 102 * a ^ 2 * b ^ 2 * c ^ 2 - 38 * a * b ^ 3 * c ^ 2 + 17 * b ^ 4 * c ^ 2 + 10 * a ^ 3 * c ^ 3 - 38 * a ^ 2 * b * c ^ 3 - 38 * a * b ^ 2 * c ^ 3 + 10 * b ^ 3 * c ^ 3 + 17 * a ^ 2 * c ^ 4 + 18 * a * b * c ^ 4 + 17 * b ^ 2 * c ^ 4 + 20 * a * c ^ 5 + 20 * b * c ^ 5 + 8 * c ^ 6 ≥ 0   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6 + 20*a^5*b + 20*a^5*c + 17*a^4*b^2 + 18*a^4*b*c + 17*a^4*c^2 + 10*a^3*b^3 - 38*a^3*b^2*c - 38*a^3*b*c^2 + 10*a^3*c^3 + 17*a^2*b^4 - 38*a^2*b^3*c - 102*a^2*b^2*c^2 - 38*a^2*b*c^3 + 17*a^2*c^4 + 20*a*b^5 + 18*a*b^4*c - 38*a*b^3*c^2 - 38*a*b^2*c^3 + 18*a*b*c^4 + 20*a*c^5 + 8*b^6 + 20*b^5*c + 17*b^4*c^2 + 10*b^3*c^3 + 17*b^2*c^4 + 20*b*c^5 + 8*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (520 : ℝ) * a^4 * (b - a)^2 + (520 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (520 : ℝ) * a^4 * (c - b)^2 + (1368 : ℝ) * a^3 * (b - a)^3 + (2052 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2108 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (712 : ℝ) * a^3 * (c - b)^3 + (1356 : ℝ) * a^2 * (b - a)^4 + (2712 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (3168 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1812 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (372 : ℝ) * a^2 * (c - b)^4 + (600 : ℝ) * a^1 * (b - a)^5 + (1500 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2032 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1548 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (592 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (88 : ℝ) * a^1 * (c - b)^5 + (100 : ℝ) * (b - a)^6 + (300 : ℝ) * (b - a)^5 * (c - b)^1 + (469 : ℝ) * (b - a)^4 * (c - b)^2 + (438 : ℝ) * (b - a)^3 * (c - b)^3 + (237 : ℝ) * (b - a)^2 * (c - b)^4 + (68 : ℝ) * (b - a)^1 * (c - b)^5 + (8 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6 + 20*a^5*b + 20*a^5*c + 17*a^4*b^2 + 18*a^4*b*c + 17*a^4*c^2 + 10*a^3*b^3 - 38*a^3*b^2*c - 38*a^3*b*c^2 + 10*a^3*c^3 + 17*a^2*b^4 - 38*a^2*b^3*c - 102*a^2*b^2*c^2 - 38*a^2*b*c^3 + 17*a^2*c^4 + 20*a*b^5 + 18*a*b^4*c - 38*a*b^3*c^2 - 38*a*b^2*c^3 + 18*a*b*c^4 + 20*a*c^5 + 8*b^6 + 20*b^5*c + 17*b^4*c^2 + 10*b^3*c^3 + 17*b^2*c^4 + 20*b*c^5 + 8*c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 8 * a ^ 6 + 20 * a ^ 5 * b + 17 * a ^ 4 * b ^ 2 + 10 * a ^ 3 * b ^ 3 + 17 * a ^ 2 * b ^ 4 + 20 * a * b ^ 5 + 8 * b ^ 6 + 20 * a ^ 5 * c + 18 * a ^ 4 * b * c - 38 * a ^ 3 * b ^ 2 * c - 38 * a ^ 2 * b ^ 3 * c + 18 * a * b ^ 4 * c + 20 * b ^ 5 * c + 17 * a ^ 4 * c ^ 2 - 38 * a ^ 3 * b * c ^ 2 - 102 * a ^ 2 * b ^ 2 * c ^ 2 - 38 * a * b ^ 3 * c ^ 2 + 17 * b ^ 4 * c ^ 2 + 10 * a ^ 3 * c ^ 3 - 38 * a ^ 2 * b * c ^ 3 - 38 * a * b ^ 2 * c ^ 3 + 10 * b ^ 3 * c ^ 3 + 17 * a ^ 2 * c ^ 4 + 18 * a * b * c ^ 4 + 17 * b ^ 2 * c ^ 4 + 20 * a * c ^ 5 + 20 * b * c ^ 5 + 8 * c ^ 6 ≥ 0) := @solution
#print axioms solution
