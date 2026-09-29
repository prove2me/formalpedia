-- Prove2me | solution 1 for WorkbookSource.base_32639
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:13.961882+00:00
-- url     : https://prove2.me/submissions/5338fc12-4b9e-4e89-aafd-82346a621d41

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^8 + b^8 + c^8 ≥ a^3 * b^3 * c^2 + b^3 * c^3 * a^2 + c^3 * a^3 * b^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^8 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^3*c^3 + b^8 + c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^6 * (b - a)^2 + (21 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^6 * (c - b)^2 + (72 : ℝ) * a^5 * (b - a)^3 + (108 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (144 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (54 : ℝ) * a^5 * (c - b)^3 + (115 : ℝ) * a^4 * (b - a)^4 + (230 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (390 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (275 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (70 : ℝ) * a^4 * (c - b)^4 + (104 : ℝ) * a^3 * (b - a)^5 + (260 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (544 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (556 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (280 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (56 : ℝ) * a^3 * (c - b)^5 + (55 : ℝ) * a^2 * (b - a)^6 + (165 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (417 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (559 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (420 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (168 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (28 : ℝ) * a^2 * (c - b)^6 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (168 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (280 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (280 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (168 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (56 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (28 : ℝ) * (b - a)^6 * (c - b)^2 + (56 : ℝ) * (b - a)^5 * (c - b)^3 + (70 : ℝ) * (b - a)^4 * (c - b)^4 + (56 : ℝ) * (b - a)^3 * (c - b)^5 + (28 : ℝ) * (b - a)^2 * (c - b)^6 + (8 : ℝ) * (b - a)^1 * (c - b)^7 + (1 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^8 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^3*c^3 + b^8 + c^8) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^8 + b^8 + c^8 ≥ a^3 * b^3 * c^2 + b^3 * c^3 * a^2 + c^3 * a^3 * b^2) := @solution
#print axioms solution
