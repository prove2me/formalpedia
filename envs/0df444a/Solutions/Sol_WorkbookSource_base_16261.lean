-- Prove2me | solution 1 for WorkbookSource.base_16261
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:47.029141+00:00
-- url     : https://prove2.me/submissions/a649e9e4-6289-4694-97f7-aecd1e3631b3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a + 5 * b) + b^2 / (2 * b + 5 * c) + c^2 / (2 * c + 5 * a)) ≥ (3 * (a^2 + b^2 + c^2)) / (7 * (a + b + c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^4*b + 25*a^4*c - 10*a^3*b^2 - 126*a^3*b*c + 185*a^3*c^2 + 185*a^2*b^3 - 84*a^2*b^2*c - 84*a^2*b*c^2 - 10*a^2*c^3 + 25*a*b^4 - 126*a*b^3*c - 84*a*b^2*c^2 - 126*a*b*c^3 + 10*a*c^4 + 10*b^4*c - 10*b^3*c^2 + 185*b^2*c^3 + 25*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (364 : ℝ) * a^3 * (b - a)^2 + (364 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (364 : ℝ) * a^3 * (c - b)^2 + (903 : ℝ) * a^2 * (b - a)^3 + (1692 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1167 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (189 : ℝ) * a^2 * (c - b)^3 + (749 : ℝ) * a^1 * (b - a)^4 + (1948 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1683 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (484 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (35 : ℝ) * a^1 * (c - b)^4 + (210 : ℝ) * (b - a)^5 + (645 : ℝ) * (b - a)^4 * (c - b)^1 + (695 : ℝ) * (b - a)^3 * (c - b)^2 + (285 : ℝ) * (b - a)^2 * (c - b)^3 + (25 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^4*b + 25*a^4*c - 10*a^3*b^2 - 126*a^3*b*c + 185*a^3*c^2 + 185*a^2*b^3 - 84*a^2*b^2*c - 84*a^2*b*c^2 - 10*a^2*c^3 + 25*a*b^4 - 126*a*b^3*c - 84*a*b^2*c^2 - 126*a*b*c^3 + 10*a*c^4 + 10*b^4*c - 10*b^3*c^2 + 185*b^2*c^3 + 25*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (364 : ℝ) * a^3 * (c - a)^2 + (364 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (364 : ℝ) * a^3 * (b - c)^2 + (903 : ℝ) * a^2 * (c - a)^3 + (1017 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (492 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (189 : ℝ) * a^2 * (b - c)^3 + (749 : ℝ) * a^1 * (c - a)^4 + (1048 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (333 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (34 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (35 : ℝ) * a^1 * (b - c)^4 + (210 : ℝ) * (c - a)^5 + (405 : ℝ) * (c - a)^4 * (b - c)^1 + (215 : ℝ) * (c - a)^3 * (b - c)^2 + (30 : ℝ) * (c - a)^2 * (b - c)^3 + (10 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^4*b + 25*a^4*c - 10*a^3*b^2 - 126*a^3*b*c + 185*a^3*c^2 + 185*a^2*b^3 - 84*a^2*b^2*c - 84*a^2*b*c^2 - 10*a^2*c^3 + 25*a*b^4 - 126*a*b^3*c - 84*a*b^2*c^2 - 126*a*b*c^3 + 10*a*c^4 + 10*b^4*c - 10*b^3*c^2 + 185*b^2*c^3 + 25*b*c^4) := by
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
  have hn : 0 ≤ (10*a^4*b + 25*a^4*c - 10*a^3*b^2 - 126*a^3*b*c + 185*a^3*c^2 + 185*a^2*b^3 - 84*a^2*b^2*c - 84*a^2*b*c^2 - 10*a^2*c^3 + 25*a*b^4 - 126*a*b^3*c - 84*a*b^2*c^2 - 126*a*b*c^3 + 10*a*c^4 + 10*b^4*c - 10*b^3*c^2 + 185*b^2*c^3 + 25*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * a + 5 * b) + b^2 / (2 * b + 5 * c) + c^2 / (2 * c + 5 * a)) ≥ (3 * (a^2 + b^2 + c^2)) / (7 * (a + b + c))) := @solution
#print axioms solution
