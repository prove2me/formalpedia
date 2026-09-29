-- Prove2me | solution 1 for WorkbookSource.plus_78986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:25.777696+00:00
-- url     : https://prove2.me/submissions/828f4d04-fad6-451d-a57b-ab166586d04c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (4 * (a + b + c) ^ 2) + 11 / 4) ≤ (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + 3*a^4*b + a^4*c - 2*a^3*c^2 - 2*a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + 3*b^4*c - 2*b^2*c^3 + b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * a^3 * (b - a)^2 + (28 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (28 : ℝ) * a^3 * (c - b)^2 + (50 : ℝ) * a^2 * (b - a)^3 + (66 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (84 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (34 : ℝ) * a^2 * (c - b)^3 + (30 : ℝ) * a^1 * (b - a)^4 + (48 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (74 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (56 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (14 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^5 + (11 : ℝ) * (b - a)^4 * (c - b)^1 + (20 : ℝ) * (b - a)^3 * (c - b)^2 + (22 : ℝ) * (b - a)^2 * (c - b)^3 + (11 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5 + 3*a^4*b + a^4*c - 2*a^3*c^2 - 2*a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + 3*b^4*c - 2*b^2*c^3 + b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * a^3 * (c - a)^2 + (28 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (28 : ℝ) * a^3 * (b - c)^2 + (50 : ℝ) * a^2 * (c - a)^3 + (84 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (102 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (34 : ℝ) * a^2 * (b - c)^3 + (30 : ℝ) * a^1 * (c - a)^4 + (72 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (110 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (68 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (14 : ℝ) * a^1 * (b - c)^4 + (6 : ℝ) * (c - a)^5 + (19 : ℝ) * (c - a)^4 * (b - c)^1 + (36 : ℝ) * (c - a)^3 * (b - c)^2 + (32 : ℝ) * (c - a)^2 * (b - c)^3 + (13 : ℝ) * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 3*a^4*b + a^4*c - 2*a^3*c^2 - 2*a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + 3*b^4*c - 2*b^2*c^3 + b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 + 3*a^4*b + a^4*c - 2*a^3*c^2 - 2*a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + 3*b^4*c - 2*b^2*c^3 + b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (4 * (a + b + c) ^ 2) + 11 / 4) ≤ (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b)) := @solution
#print axioms solution
