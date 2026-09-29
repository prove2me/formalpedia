-- Prove2me | solution 1 for WorkbookSource.plus_44406
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:12.036466+00:00
-- url     : https://prove2.me/submissions/418903f7-4116-42eb-91ef-c6775d9ebf69

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 18 * a * b * c * (a * (a + b) * (a + c) + b * (b + a) * (b + c) + c * (c + a) * (c + b)) ≤ (a + b + c) ^ 3 * (a + b) * (b + c) * (c + a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + a^5*c + 4*a^4*b^2 - 10*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 + a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 24*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + a*b^5 - 10*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 10*a*b*c^4 + a*c^5 + b^5*c + 4*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (b - a)^2 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^4 * (c - b)^2 + (118 : ℝ) * a^3 * (b - a)^3 + (177 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (111 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (26 : ℝ) * a^3 * (c - b)^3 + (146 : ℝ) * a^2 * (b - a)^4 + (292 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (201 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (55 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^2 * (c - b)^4 + (80 : ℝ) * a^1 * (b - a)^5 + (200 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (178 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (67 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (13 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (56 : ℝ) * (b - a)^4 * (c - b)^2 + (32 : ℝ) * (b - a)^3 * (c - b)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c + 4*a^4*b^2 - 10*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 + a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 24*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + a*b^5 - 10*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 10*a*b*c^4 + a*c^5 + b^5*c + 4*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4 + b*c^5) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 18 * a * b * c * (a * (a + b) * (a + c) + b * (b + a) * (b + c) + c * (c + a) * (c + b)) ≤ (a + b + c) ^ 3 * (a + b) * (b + c) * (c + a)) := @solution
#print axioms solution
