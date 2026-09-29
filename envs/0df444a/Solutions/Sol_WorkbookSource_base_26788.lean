-- Prove2me | solution 1 for WorkbookSource.base_26788
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:30.853578+00:00
-- url     : https://prove2.me/submissions/9f8f3545-609b-49c1-821c-9ca05874e9ad

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) * (a + b + c)^2 ≥ 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 * (a^2 + b^2 + c^2)  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b^2 - 6*a^6*b*c + 5*a^6*c^2 + 10*a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + 10*a^5*c^3 + 10*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 8*a^4*b*c^3 + 10*a^4*c^4 + 10*a^3*b^5 - 8*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 + 5*a^2*b^6 - 2*a^2*b^5*c - 4*a^2*b^4*c^2 - 10*a^2*b^3*c^3 - 4*a^2*b^2*c^4 - 2*a^2*b*c^5 + 5*a^2*c^6 - 6*a*b^6*c - 2*a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 - 2*a*b^2*c^5 - 6*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3 + 10*b^4*c^4 + 10*b^3*c^5 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (160 : ℝ) * a^6 * (b - a)^2 + (160 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (160 : ℝ) * a^6 * (c - b)^2 + (736 : ℝ) * a^5 * (b - a)^3 + (1104 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (816 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (224 : ℝ) * a^5 * (c - b)^3 + (1420 : ℝ) * a^4 * (b - a)^4 + (2840 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2260 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (840 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (140 : ℝ) * a^4 * (c - b)^4 + (1480 : ℝ) * a^3 * (b - a)^5 + (3700 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3560 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1640 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (380 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (40 : ℝ) * a^3 * (c - b)^5 + (884 : ℝ) * a^2 * (b - a)^6 + (2652 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (3127 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1834 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (547 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (72 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (4 : ℝ) * a^2 * (c - b)^6 + (288 : ℝ) * a^1 * (b - a)^7 + (1008 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1436 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1070 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (432 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (82 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (40 : ℝ) * (b - a)^8 + (160 : ℝ) * (b - a)^7 * (c - b)^1 + (270 : ℝ) * (b - a)^6 * (c - b)^2 + (250 : ℝ) * (b - a)^5 * (c - b)^3 + (135 : ℝ) * (b - a)^4 * (c - b)^4 + (40 : ℝ) * (b - a)^3 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b^2 - 6*a^6*b*c + 5*a^6*c^2 + 10*a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + 10*a^5*c^3 + 10*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 8*a^4*b*c^3 + 10*a^4*c^4 + 10*a^3*b^5 - 8*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 + 5*a^2*b^6 - 2*a^2*b^5*c - 4*a^2*b^4*c^2 - 10*a^2*b^3*c^3 - 4*a^2*b^2*c^4 - 2*a^2*b*c^5 + 5*a^2*c^6 - 6*a*b^6*c - 2*a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 - 2*a*b^2*c^5 - 6*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3 + 10*b^4*c^4 + 10*b^3*c^5 + 5*b^2*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 8 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) * (a + b + c)^2 ≥ 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
