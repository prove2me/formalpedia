-- Prove2me | solution 1 for WorkbookSource.plus_14843
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:26:55.897815+00:00
-- url     : https://prove2.me/submissions/8a4ba3f8-e879-4708-a3cf-8e9c0ca25b8b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a * b + b * c + c * a) ≥ 3 * a * b * c * (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b + 2*a^4*c - 7*a^3*b*c + 3*a^2*b^2*c + 3*a^2*b*c^2 + 2*a*b^4 - 7*a*b^3*c + 3*a*b^2*c^2 - 7*a*b*c^3 + 2*a*c^4 + 2*b^4*c + 2*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^3 * (b - a)^2 + (9 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^3 * (c - b)^2 + (18 : ℝ) * a^2 * (b - a)^3 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (27 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^2 * (c - b)^3 + (13 : ℝ) * a^1 * (b - a)^4 + (26 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (30 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (17 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (12 : ℝ) * (b - a)^3 * (c - b)^2 + (8 : ℝ) * (b - a)^2 * (c - b)^3 + (2 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b + 2*a^4*c - 7*a^3*b*c + 3*a^2*b^2*c + 3*a^2*b*c^2 + 2*a*b^4 - 7*a*b^3*c + 3*a*b^2*c^2 - 7*a*b*c^3 + 2*a*c^4 + 2*b^4*c + 2*b*c^4) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a * b + b * c + c * a) ≥ 3 * a * b * c * (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a))) := @solution
#print axioms solution
