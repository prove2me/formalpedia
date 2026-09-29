-- Prove2me | solution 1 for WorkbookSource.base_960
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:24.097897+00:00
-- url     : https://prove2.me/submissions/e7e24c71-5a42-4cb0-bdaa-307a58f7cc70

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2)) ≥ 7 / 3 * (a + b + c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) + a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b + 3*a^6*c - a^5*b^2 + 2*a^5*b*c - a^5*c^2 - 2*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 - 2*a^3*b^3*c + 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - 2*a^3*c^4 - a^2*b^5 - a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 - a^2*c^5 + 3*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 3*a*c^6 + 3*b^6*c - b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 - b^2*c^5 + 3*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^5 * (b - a)^2 + (36 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^5 * (c - b)^2 + (90 : ℝ) * a^4 * (b - a)^3 + (135 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (225 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (90 : ℝ) * a^4 * (c - b)^3 + (84 : ℝ) * a^3 * (b - a)^4 + (168 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (432 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (348 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (84 : ℝ) * a^3 * (c - b)^4 + (36 : ℝ) * a^2 * (b - a)^5 + (90 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (360 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (450 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (216 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (36 : ℝ) * a^2 * (c - b)^5 + (6 : ℝ) * a^1 * (b - a)^6 + (18 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (132 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (234 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (168 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (54 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (6 : ℝ) * a^1 * (c - b)^6 + (16 : ℝ) * (b - a)^5 * (c - b)^2 + (40 : ℝ) * (b - a)^4 * (c - b)^3 + (38 : ℝ) * (b - a)^3 * (c - b)^4 + (17 : ℝ) * (b - a)^2 * (c - b)^5 + (3 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b + 3*a^6*c - a^5*b^2 + 2*a^5*b*c - a^5*c^2 - 2*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 - 2*a^3*b^3*c + 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - 2*a^3*c^4 - a^2*b^5 - a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 - a^2*c^5 + 3*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 3*a*c^6 + 3*b^6*c - b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 - b^2*c^5 + 3*b*c^6) := by
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
  have hn : 0 ≤ (3*a^6*b + 3*a^6*c - a^5*b^2 + 2*a^5*b*c - a^5*c^2 - 2*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 - 2*a^3*b^3*c + 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - 2*a^3*c^4 - a^2*b^5 - a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 - a^2*c^5 + 3*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 3*a*c^6 + 3*b^6*c - b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 - b^2*c^5 + 3*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2)) ≥ 7 / 3 * (a + b + c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) + a * b * c)) := @solution
#print axioms solution
