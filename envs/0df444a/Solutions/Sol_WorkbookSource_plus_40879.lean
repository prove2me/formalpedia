-- Prove2me | solution 1 for WorkbookSource.plus_40879
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:35:52.817476+00:00
-- url     : https://prove2.me/submissions/78415f85-008c-4b1e-83f9-ff6561f1eeb5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a * b + a * c + b * c) * (a + b + c) ^ 4 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (27*a^6 - a^5*b - a^5*c - 4*a^4*b^2 - 9*a^4*b*c - 4*a^4*c^2 + 48*a^3*b^3 - 22*a^3*b^2*c - 22*a^3*b*c^2 + 48*a^3*c^3 - 4*a^2*b^4 - 22*a^2*b^3*c - 36*a^2*b^2*c^2 - 22*a^2*b*c^3 - 4*a^2*c^4 - a*b^5 - 9*a*b^4*c - 22*a*b^3*c^2 - 22*a*b^2*c^3 - 9*a*b*c^4 - a*c^5 + 27*b^6 - b^5*c - 4*b^4*c^2 + 48*b^3*c^3 - 4*b^2*c^4 - b*c^5 + 27*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (351 : ℝ) * a^4 * (b - a)^2 + (351 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (351 : ℝ) * a^4 * (c - b)^2 + (900 : ℝ) * a^3 * (b - a)^3 + (1350 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1458 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (504 : ℝ) * a^3 * (c - b)^3 + (972 : ℝ) * a^2 * (b - a)^4 + (1944 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2484 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1512 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (378 : ℝ) * a^2 * (c - b)^4 + (488 : ℝ) * a^1 * (b - a)^5 + (1220 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1892 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1618 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (778 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (160 : ℝ) * a^1 * (c - b)^5 + (92 : ℝ) * (b - a)^6 + (276 : ℝ) * (b - a)^5 * (c - b)^1 + (511 : ℝ) * (b - a)^4 * (c - b)^2 + (562 : ℝ) * (b - a)^3 * (c - b)^3 + (396 : ℝ) * (b - a)^2 * (c - b)^4 + (161 : ℝ) * (b - a)^1 * (c - b)^5 + (27 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (27*a^6 - a^5*b - a^5*c - 4*a^4*b^2 - 9*a^4*b*c - 4*a^4*c^2 + 48*a^3*b^3 - 22*a^3*b^2*c - 22*a^3*b*c^2 + 48*a^3*c^3 - 4*a^2*b^4 - 22*a^2*b^3*c - 36*a^2*b^2*c^2 - 22*a^2*b*c^3 - 4*a^2*c^4 - a*b^5 - 9*a*b^4*c - 22*a*b^3*c^2 - 22*a*b^2*c^3 - 9*a*b*c^4 - a*c^5 + 27*b^6 - b^5*c - 4*b^4*c^2 + 48*b^3*c^3 - 4*b^2*c^4 - b*c^5 + 27*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a * b + a * c + b * c) * (a + b + c) ^ 4 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2) := @solution
#print axioms solution
