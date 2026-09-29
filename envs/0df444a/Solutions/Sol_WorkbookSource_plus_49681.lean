-- Prove2me | solution 1 for WorkbookSource.plus_49681
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:14.361744+00:00
-- url     : https://prove2.me/submissions/13952edc-96c5-4854-9570-660874e7bf3a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 5 ≥ 81 * (a + b - c) * (a - b + c) * (-a + b + c) * (a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 + 86*a^4*b + 86*a^4*c - 71*a^3*b^2 - 61*a^3*b*c - 71*a^3*c^2 - 71*a^2*b^3 + 30*a^2*b^2*c + 30*a^2*b*c^2 - 71*a^2*c^3 + 86*a*b^4 - 61*a*b^3*c + 30*a*b^2*c^2 - 61*a*b*c^3 + 86*a*c^4 + b^5 + 86*b^4*c - 71*b^3*c^2 - 71*b^2*c^3 + 86*b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (351 : ℝ) * a^3 * (b - a)^2 + (351 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (351 : ℝ) * a^3 * (c - b)^2 + (558 : ℝ) * a^2 * (b - a)^3 + (837 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1269 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (495 : ℝ) * a^2 * (c - b)^3 + (240 : ℝ) * a^1 * (b - a)^4 + (480 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1089 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (849 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (177 : ℝ) * a^1 * (c - b)^4 + (32 : ℝ) * (b - a)^5 + (80 : ℝ) * (b - a)^4 * (c - b)^1 + (242 : ℝ) * (b - a)^3 * (c - b)^2 + (283 : ℝ) * (b - a)^2 * (c - b)^3 + (91 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 + 86*a^4*b + 86*a^4*c - 71*a^3*b^2 - 61*a^3*b*c - 71*a^3*c^2 - 71*a^2*b^3 + 30*a^2*b^2*c + 30*a^2*b*c^2 - 71*a^2*c^3 + 86*a*b^4 - 61*a*b^3*c + 30*a*b^2*c^2 - 61*a*b*c^3 + 86*a*c^4 + b^5 + 86*b^4*c - 71*b^3*c^2 - 71*b^2*c^3 + 86*b*c^4 + c^5) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 5 ≥ 81 * (a + b - c) * (a - b + c) * (-a + b + c) * (a * b + b * c + c * a)) := @solution
#print axioms solution
