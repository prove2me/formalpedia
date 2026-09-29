-- Prove2me | solution 1 for WorkbookSource.plus_27702
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:34:38.64802+00:00
-- url     : https://prove2.me/submissions/4290dc7a-e2c2-410b-bdcd-da6b467243df

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a > 0) : 2 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (b + c) * (c + a) + (b - c) ^ 2 * (b + c - a) ^ 2 * (c + a) * (a + b) + (c - a) ^ 2 * (c + a - b) ^ 2 * (a + b) * (b + c)) ≥ 3 * ((a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b + 4*a^5*c - 3*a^4*b^2 - 2*a^4*b*c - 3*a^4*c^2 - 2*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 - 3*a^2*b^4 - 2*a^2*b^3*c + 18*a^2*b^2*c^2 - 2*a^2*b*c^3 - 3*a^2*c^4 + 4*a*b^5 - 2*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 - 2*a*b*c^4 + 4*a*c^5 + 4*b^5*c - 3*b^4*c^2 - 2*b^3*c^3 - 3*b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (b - a)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (24 : ℝ) * a^3 * (b - a)^3 + (36 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (92 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (40 : ℝ) * a^3 * (c - b)^3 + (8 : ℝ) * a^2 * (b - a)^4 + (16 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (132 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (124 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (32 : ℝ) * a^2 * (c - b)^4 + (72 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (108 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (52 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^1 * (c - b)^5 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (26 : ℝ) * (b - a)^3 * (c - b)^3 + (17 : ℝ) * (b - a)^2 * (c - b)^4 + (4 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b + 4*a^5*c - 3*a^4*b^2 - 2*a^4*b*c - 3*a^4*c^2 - 2*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 - 3*a^2*b^4 - 2*a^2*b^3*c + 18*a^2*b^2*c^2 - 2*a^2*b*c^3 - 3*a^2*c^4 + 4*a*b^5 - 2*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 - 2*a*b*c^4 + 4*a*c^5 + 4*b^5*c - 3*b^4*c^2 - 2*b^3*c^3 - 3*b^2*c^4 + 4*b*c^5) := by
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
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a > 0), 2 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (b + c) * (c + a) + (b - c) ^ 2 * (b + c - a) ^ 2 * (c + a) * (a + b) + (c - a) ^ 2 * (c + a - b) ^ 2 * (a + b) * (b + c)) ≥ 3 * ((a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2)) := @solution
#print axioms solution
