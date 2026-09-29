-- Prove2me | solution 1 for WorkbookSource.plus_12674
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:26:54.520563+00:00
-- url     : https://prove2.me/submissions/97d8545e-754f-41a9-ad7c-bf798d28a3c8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b - c) * (a + c - b) * (b + c - a) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ a * b * c * (a * b + a * c + b * c) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 - a^6*b - a^6*c + a^5*b^2 + 2*a^5*b*c + a^5*c^2 - a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + 5*a^3*b^3*c + 5*a^3*b*c^3 - a^3*c^4 + a^2*b^5 - 3*a^2*b^4*c - 3*a^2*b*c^4 + a^2*c^5 - a*b^6 + 2*a*b^5*c - 3*a*b^4*c^2 + 5*a*b^3*c^3 - 3*a*b^2*c^4 + 2*a*b*c^5 - a*c^6 + b^7 - b^6*c + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 - b*c^6 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^5 * (b - a)^2 + (3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^5 * (c - b)^2 + (4 : ℝ) * a^4 * (b - a)^3 + (6 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (11 : ℝ) * a^4 * (c - b)^3 + (3 : ℝ) * a^3 * (b - a)^4 + (6 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (59 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (56 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (17 : ℝ) * a^3 * (c - b)^4 + (2 : ℝ) * a^2 * (b - a)^5 + (5 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (68 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (97 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (58 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (13 : ℝ) * a^2 * (c - b)^5 + (1 : ℝ) * a^1 * (b - a)^6 + (3 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (39 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (73 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (64 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (28 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (5 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^5 * (c - b)^2 + (20 : ℝ) * (b - a)^4 * (c - b)^3 + (24 : ℝ) * (b - a)^3 * (c - b)^4 + (16 : ℝ) * (b - a)^2 * (c - b)^5 + (6 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 - a^6*b - a^6*c + a^5*b^2 + 2*a^5*b*c + a^5*c^2 - a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + 5*a^3*b^3*c + 5*a^3*b*c^3 - a^3*c^4 + a^2*b^5 - 3*a^2*b^4*c - 3*a^2*b*c^4 + a^2*c^5 - a*b^6 + 2*a*b^5*c - 3*a*b^4*c^2 + 5*a*b^3*c^3 - 3*a*b^2*c^4 + 2*a*b*c^5 - a*c^6 + b^7 - b^6*c + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 - b*c^6 + c^7) := by
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
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + b - c) * (a + c - b) * (b + c - a) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ a * b * c * (a * b + a * c + b * c) ^ 2) := @solution
#print axioms solution
