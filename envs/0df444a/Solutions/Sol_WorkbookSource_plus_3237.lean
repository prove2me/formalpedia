-- Prove2me | solution 1 for WorkbookSource.plus_3237
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:05.858085+00:00
-- url     : https://prove2.me/submissions/cb7de914-4cba-4ee8-a6e2-c88986284be3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) * (b ^ 2 + b * c + c ^ 2) + (b - c) ^ 2 * (b + c - a) ^ 2 * (b ^ 2 + b * a + a ^ 2) * (c ^ 2 + c * a + a ^ 2) + (c - a) ^ 2 * (c + a - b) ^ 2 * (c ^ 2 + c * b + b ^ 2) * (a ^ 2 + a * b + b ^ 2)) ≥ 4 * (a + b + c) ^ 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b^2 + 8*a^6*b*c + 5*a^6*c^2 - 6*a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 - 6*a^5*c^3 + 2*a^4*b^4 - 5*a^4*b^3*c + 6*a^4*b^2*c^2 - 5*a^4*b*c^3 + 2*a^4*c^4 - 6*a^3*b^5 - 5*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^3*b*c^4 - 6*a^3*c^5 + 5*a^2*b^6 - 3*a^2*b^5*c + 6*a^2*b^4*c^2 + 2*a^2*b^3*c^3 + 6*a^2*b^2*c^4 - 3*a^2*b*c^5 + 5*a^2*c^6 + 8*a*b^6*c - 3*a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 - 3*a*b^2*c^5 + 8*a*b*c^6 + 5*b^6*c^2 - 6*b^5*c^3 + 2*b^4*c^4 - 6*b^3*c^5 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (54 : ℝ) * a^6 * (b - a)^2 + (54 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (54 : ℝ) * a^6 * (c - b)^2 + (162 : ℝ) * a^5 * (b - a)^3 + (243 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (405 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (162 : ℝ) * a^5 * (c - b)^3 + (180 : ℝ) * a^4 * (b - a)^4 + (360 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (945 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (765 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (180 : ℝ) * a^4 * (c - b)^4 + (90 : ℝ) * a^3 * (b - a)^5 + (225 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (990 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1260 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (585 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (90 : ℝ) * a^3 * (c - b)^5 + (18 : ℝ) * a^2 * (b - a)^6 + (54 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (513 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (936 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (648 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (189 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (18 : ℝ) * a^2 * (c - b)^6 + (126 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (315 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (288 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (117 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (42 : ℝ) * (b - a)^5 * (c - b)^3 + (47 : ℝ) * (b - a)^4 * (c - b)^4 + (24 : ℝ) * (b - a)^3 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b^2 + 8*a^6*b*c + 5*a^6*c^2 - 6*a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 - 6*a^5*c^3 + 2*a^4*b^4 - 5*a^4*b^3*c + 6*a^4*b^2*c^2 - 5*a^4*b*c^3 + 2*a^4*c^4 - 6*a^3*b^5 - 5*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^3*b*c^4 - 6*a^3*c^5 + 5*a^2*b^6 - 3*a^2*b^5*c + 6*a^2*b^4*c^2 + 2*a^2*b^3*c^3 + 6*a^2*b^2*c^4 - 3*a^2*b*c^5 + 5*a^2*c^6 + 8*a*b^6*c - 3*a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 - 3*a*b^2*c^5 + 8*a*b*c^6 + 5*b^6*c^2 - 6*b^5*c^3 + 2*b^4*c^4 - 6*b^3*c^5 + 5*b^2*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 3 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) * (b ^ 2 + b * c + c ^ 2) + (b - c) ^ 2 * (b + c - a) ^ 2 * (b ^ 2 + b * a + a ^ 2) * (c ^ 2 + c * a + a ^ 2) + (c - a) ^ 2 * (c + a - b) ^ 2 * (c ^ 2 + c * b + b ^ 2) * (a ^ 2 + a * b + b ^ 2)) ≥ 4 * (a + b + c) ^ 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2) := @solution
#print axioms solution
