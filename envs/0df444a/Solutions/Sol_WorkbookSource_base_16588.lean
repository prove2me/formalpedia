-- Prove2me | solution 1 for WorkbookSource.base_16588
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:41.696336+00:00
-- url     : https://prove2.me/submissions/e3f91f10-5773-4e67-925f-3fd73a75884a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a ^ 6 + b ^ 6 + c ^ 6) + 5 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6 - 3*a^4*b^2 + 5*a^4*b*c - 3*a^4*c^2 - 3*a^2*b^4 - 6*a^2*b^2*c^2 - 3*a^2*c^4 + 5*a*b^4*c + 5*a*b*c^4 + 3*b^6 - 3*b^4*c^2 - 3*b^2*c^4 + 3*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^4 * (b - a)^2 + (27 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^4 * (c - b)^2 + (52 : ℝ) * a^3 * (b - a)^3 + (78 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (138 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (56 : ℝ) * a^3 * (c - b)^3 + (38 : ℝ) * a^2 * (b - a)^4 + (76 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (210 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (172 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (44 : ℝ) * a^2 * (c - b)^4 + (10 : ℝ) * a^1 * (b - a)^5 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (126 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (164 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (89 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^1 * (c - b)^5 + (24 : ℝ) * (b - a)^4 * (c - b)^2 + (48 : ℝ) * (b - a)^3 * (c - b)^3 + (42 : ℝ) * (b - a)^2 * (c - b)^4 + (18 : ℝ) * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6 - 3*a^4*b^2 + 5*a^4*b*c - 3*a^4*c^2 - 3*a^2*b^4 - 6*a^2*b^2*c^2 - 3*a^2*c^4 + 5*a*b^4*c + 5*a*b*c^4 + 3*b^6 - 3*b^4*c^2 - 3*b^2*c^4 + 3*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 4 * (a ^ 6 + b ^ 6 + c ^ 6) + 5 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3) := @solution
#print axioms solution
