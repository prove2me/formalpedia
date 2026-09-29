-- Prove2me | solution 1 for WorkbookSource.base_8483
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:18.763667+00:00
-- url     : https://prove2.me/submissions/e21ffa95-eafb-43d8-bda6-c8b62f581672

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 / (b + c) + b^4 / (a + c) + c^4 / (a + b)) ≥ (1 / 18) * (a + b + c)^3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (18*a^6 + 17*a^5*b + 17*a^5*c - 4*a^4*b^2 + 10*a^4*b*c - 4*a^4*c^2 - 6*a^3*b^3 - 19*a^3*b^2*c - 19*a^3*b*c^2 - 6*a^3*c^3 - 4*a^2*b^4 - 19*a^2*b^3*c - 30*a^2*b^2*c^2 - 19*a^2*b*c^3 - 4*a^2*c^4 + 17*a*b^5 + 10*a*b^4*c - 19*a*b^3*c^2 - 19*a*b^2*c^3 + 10*a*b*c^4 + 17*a*c^5 + 18*b^6 + 17*b^5*c - 4*b^4*c^2 - 6*b^3*c^3 - 4*b^2*c^4 + 17*b*c^5 + 18*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (396 : ℝ) * a^4 * (b - a)^2 + (396 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (396 : ℝ) * a^4 * (c - b)^2 + (926 : ℝ) * a^3 * (b - a)^3 + (1389 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1779 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (658 : ℝ) * a^3 * (c - b)^3 + (844 : ℝ) * a^2 * (b - a)^4 + (1688 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2715 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1871 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (442 : ℝ) * a^2 * (c - b)^4 + (352 : ℝ) * a^1 * (b - a)^5 + (880 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1730 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1715 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (797 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (142 : ℝ) * a^1 * (c - b)^5 + (56 : ℝ) * (b - a)^6 + (168 : ℝ) * (b - a)^5 * (c - b)^1 + (394 : ℝ) * (b - a)^4 * (c - b)^2 + (508 : ℝ) * (b - a)^3 * (c - b)^3 + (351 : ℝ) * (b - a)^2 * (c - b)^4 + (125 : ℝ) * (b - a)^1 * (c - b)^5 + (18 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (18*a^6 + 17*a^5*b + 17*a^5*c - 4*a^4*b^2 + 10*a^4*b*c - 4*a^4*c^2 - 6*a^3*b^3 - 19*a^3*b^2*c - 19*a^3*b*c^2 - 6*a^3*c^3 - 4*a^2*b^4 - 19*a^2*b^3*c - 30*a^2*b^2*c^2 - 19*a^2*b*c^3 - 4*a^2*c^4 + 17*a*b^5 + 10*a*b^4*c - 19*a*b^3*c^2 - 19*a*b^2*c^3 + 10*a*b*c^4 + 17*a*c^5 + 18*b^6 + 17*b^5*c - 4*b^4*c^2 - 6*b^3*c^3 - 4*b^2*c^4 + 17*b*c^5 + 18*c^6) := by
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
  have hn : 0 ≤ (18*a^6 + 17*a^5*b + 17*a^5*c - 4*a^4*b^2 + 10*a^4*b*c - 4*a^4*c^2 - 6*a^3*b^3 - 19*a^3*b^2*c - 19*a^3*b*c^2 - 6*a^3*c^3 - 4*a^2*b^4 - 19*a^2*b^3*c - 30*a^2*b^2*c^2 - 19*a^2*b*c^3 - 4*a^2*c^4 + 17*a*b^5 + 10*a*b^4*c - 19*a*b^3*c^2 - 19*a*b^2*c^3 + 10*a*b*c^4 + 17*a*c^5 + 18*b^6 + 17*b^5*c - 4*b^4*c^2 - 6*b^3*c^3 - 4*b^2*c^4 + 17*b*c^5 + 18*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^4 / (b + c) + b^4 / (a + c) + c^4 / (a + b)) ≥ (1 / 18) * (a + b + c)^3) := @solution
#print axioms solution
