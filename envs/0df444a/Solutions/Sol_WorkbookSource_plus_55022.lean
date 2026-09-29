-- Prove2me | solution 1 for WorkbookSource.plus_55022
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:38.537003+00:00
-- url     : https://prove2.me/submissions/4b11d31e-8bae-4f4e-842f-5b271bc3a74a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 - b^5) * (a - b) + (b^5 - c^5) * (b - c) + (c^5 - a^5) * (c - a) ≥ 5 * a * b * (a^2 + b^2 - a * c - b * c) * (a - b)^2 + 5 * b * c * (b^2 + c^2 - b * a - c * a) * (b - c)^2 + 5 * c * a * (c^2 + a^2 - c * b - a * b) * (c - a)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 - 6*a^5*b - 6*a^5*c + 10*a^4*b^2 + 10*a^4*b*c + 10*a^4*c^2 - 10*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 - 10*a^3*c^3 + 10*a^2*b^4 - 5*a^2*b^3*c - 5*a^2*b*c^3 + 10*a^2*c^4 - 6*a*b^5 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 - 6*a*c^5 + 2*b^6 - 6*b^5*c + 10*b^4*c^2 - 10*b^3*c^3 + 10*b^2*c^4 - 6*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^4 * (b - a)^2 + (10 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (10 : ℝ) * a^4 * (c - b)^2 + (30 : ℝ) * a^3 * (b - a)^3 + (45 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (35 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^3 * (c - b)^3 + (30 : ℝ) * a^2 * (b - a)^4 + (60 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (45 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^5 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (20 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (5 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * (b - a)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (10 : ℝ) * (b - a)^4 * (c - b)^2 + (10 : ℝ) * (b - a)^3 * (c - b)^3 + (10 : ℝ) * (b - a)^2 * (c - b)^4 + (6 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 - 6*a^5*b - 6*a^5*c + 10*a^4*b^2 + 10*a^4*b*c + 10*a^4*c^2 - 10*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 - 10*a^3*c^3 + 10*a^2*b^4 - 5*a^2*b^3*c - 5*a^2*b*c^3 + 10*a^2*c^4 - 6*a*b^5 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 - 6*a*c^5 + 2*b^6 - 6*b^5*c + 10*b^4*c^2 - 10*b^3*c^3 + 10*b^2*c^4 - 6*b*c^5 + 2*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^5 - b^5) * (a - b) + (b^5 - c^5) * (b - c) + (c^5 - a^5) * (c - a) ≥ 5 * a * b * (a^2 + b^2 - a * c - b * c) * (a - b)^2 + 5 * b * c * (b^2 + c^2 - b * a - c * a) * (b - c)^2 + 5 * c * a * (c^2 + a^2 - c * b - a * b) * (c - a)^2) := @solution
#print axioms solution
