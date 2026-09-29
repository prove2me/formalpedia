-- Prove2me | solution 1 for WorkbookSource.base_35760
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:06:08.128309+00:00
-- url     : https://prove2.me/submissions/3514420d-6f2e-4009-a55b-bb59a5f8d4de

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) + 1 / 2 ≥ (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 - 2*a^4*b - 2*a^4*c + a^3*b^2 + 7*a^3*b*c + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + a^2*c^3 - 2*a*b^4 + 7*a*b^3*c - 6*a*b^2*c^2 + 7*a*b*c^3 - 2*a*c^4 + b^5 - 2*b^4*c + b^3*c^2 + b^2*c^3 - 2*b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^3 * (b - a)^2 + (3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^3 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^3 + (9 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^4 + (8 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (5 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^2 + (3 : ℝ) * (b - a)^2 * (c - b)^3 + (3 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 - 2*a^4*b - 2*a^4*c + a^3*b^2 + 7*a^3*b*c + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + a^2*c^3 - 2*a*b^4 + 7*a*b^3*c - 6*a*b^2*c^2 + 7*a*b*c^3 - 2*a*c^4 + b^5 - 2*b^4*c + b^3*c^2 + b^2*c^3 - 2*b*c^4 + c^5) := by
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
  have hn : 0 ≤ ((a^2 - a*b - a*c + b^2 - b*c + c^2)*(a^3 - a^2*b - a^2*c - a*b^2 + 6*a*b*c - a*c^2 + b^3 - b^2*c - b*c^2 + c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) + 1 / 2 ≥ (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
