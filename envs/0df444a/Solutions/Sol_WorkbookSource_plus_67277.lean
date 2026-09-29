-- Prove2me | solution 1 for WorkbookSource.plus_67277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:46:55.786786+00:00
-- url     : https://prove2.me/submissions/e1afb419-34bc-4a5f-8071-68701fa4337d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 6 / (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b + 2*a^5*c + 6*a^4*b^2 - 7*a^4*b*c + 6*a^4*c^2 - 16*a^3*b^3 + 10*a^3*b^2*c + 10*a^3*b*c^2 - 16*a^3*c^3 + 6*a^2*b^4 + 10*a^2*b^3*c - 39*a^2*b^2*c^2 + 10*a^2*b*c^3 + 6*a^2*c^4 + 2*a*b^5 - 7*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 7*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 6*b^4*c^2 - 16*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^4 * (b - a)^2 + (27 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^4 * (c - b)^2 + (60 : ℝ) * a^3 * (b - a)^3 + (90 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (126 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (48 : ℝ) * a^3 * (c - b)^3 + (43 : ℝ) * a^2 * (b - a)^4 + (86 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (165 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (122 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (25 : ℝ) * a^2 * (c - b)^4 + (10 : ℝ) * a^1 * (b - a)^5 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (74 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (86 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (35 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (14 : ℝ) * (b - a)^4 * (c - b)^2 + (28 : ℝ) * (b - a)^3 * (c - b)^3 + (16 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b + 2*a^5*c + 6*a^4*b^2 - 7*a^4*b*c + 6*a^4*c^2 - 16*a^3*b^3 + 10*a^3*b^2*c + 10*a^3*b*c^2 - 16*a^3*c^3 + 6*a^2*b^4 + 10*a^2*b^3*c - 39*a^2*b^2*c^2 + 10*a^2*b*c^3 + 6*a^2*c^4 + 2*a*b^5 - 7*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 7*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 6*b^4*c^2 - 16*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b + 2*a^5*c + 6*a^4*b^2 - 7*a^4*b*c + 6*a^4*c^2 - 16*a^3*b^3 + 10*a^3*b^2*c + 10*a^3*b*c^2 - 16*a^3*c^3 + 6*a^2*b^4 + 10*a^2*b^3*c - 39*a^2*b^2*c^2 + 10*a^2*b*c^3 + 6*a^2*c^4 + 2*a*b^5 - 7*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 7*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 6*b^4*c^2 - 16*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 6 / (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)) := @solution
#print axioms solution
