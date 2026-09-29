-- Prove2me | solution 1 for WorkbookSource.base_2207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:57:14.848996+00:00
-- url     : https://prove2.me/submissions/bf8345a2-ae77-48ab-8bdf-b8d9db17629e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (7 * a + b + c) + 1 / (a + 7 * b + c) + 1 / (a + b + 7 * c)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^5 + 60*a^4*b + 60*a^4*c - 66*a^3*b^2 + 546*a^3*b*c - 66*a^3*c^2 - 66*a^2*b^3 - 540*a^2*b^2*c - 540*a^2*b*c^2 - 66*a^2*c^3 + 60*a*b^4 + 546*a*b^3*c - 540*a*b^2*c^2 + 546*a*b*c^3 + 60*a*c^4 + 6*b^5 + 60*b^4*c - 66*b^3*c^2 - 66*b^2*c^3 + 60*b*c^4 + 6*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (810 : ℝ) * a^3 * (b - a)^2 + (810 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (810 : ℝ) * a^3 * (c - b)^2 + (1476 : ℝ) * a^2 * (b - a)^3 + (2214 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (2646 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (954 : ℝ) * a^2 * (c - b)^3 + (672 : ℝ) * a^1 * (b - a)^4 + (1344 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1926 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (1254 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (150 : ℝ) * a^1 * (c - b)^4 + (156 : ℝ) * (b - a)^3 * (c - b)^2 + (234 : ℝ) * (b - a)^2 * (c - b)^3 + (90 : ℝ) * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^5 + 60*a^4*b + 60*a^4*c - 66*a^3*b^2 + 546*a^3*b*c - 66*a^3*c^2 - 66*a^2*b^3 - 540*a^2*b^2*c - 540*a^2*b*c^2 - 66*a^2*c^3 + 60*a*b^4 + 546*a*b^3*c - 540*a*b^2*c^2 + 546*a*b*c^3 + 60*a*c^4 + 6*b^5 + 60*b^4*c - 66*b^3*c^2 - 66*b^2*c^3 + 60*b*c^4 + 6*c^5) := by
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
  have hn : 0 ≤ (6*a^5 + 60*a^4*b + 60*a^4*c - 66*a^3*b^2 + 546*a^3*b*c - 66*a^3*c^2 - 66*a^2*b^3 - 540*a^2*b^2*c - 540*a^2*b*c^2 - 66*a^2*c^3 + 60*a*b^4 + 546*a*b^3*c - 540*a*b^2*c^2 + 546*a*b*c^3 + 60*a*c^4 + 6*b^5 + 60*b^4*c - 66*b^3*c^2 - 66*b^2*c^3 + 60*b*c^4 + 6*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (7 * a + b + c) + 1 / (a + 7 * b + c) + 1 / (a + b + 7 * c)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 3)) := @solution
#print axioms solution
