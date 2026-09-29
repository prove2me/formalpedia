-- Prove2me | solution 1 for WorkbookSource.plus_89
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:33.763031+00:00
-- url     : https://prove2.me/submissions/39542d3a-d636-4f2a-b430-8c2860d5268a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * (a - b) * (a - c) + b^4 * (b - a) * (b - c) + c^4 * (c - a) * (c - b) ≥ 5 * (b - c)^2 * (c - a)^2 * (a - b)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 - a^5*b - a^5*c - 5*a^4*b^2 + 11*a^4*b*c - 5*a^4*c^2 + 10*a^3*b^3 - 10*a^3*b^2*c - 10*a^3*b*c^2 + 10*a^3*c^3 - 5*a^2*b^4 - 10*a^2*b^3*c + 30*a^2*b^2*c^2 - 10*a^2*b*c^3 - 5*a^2*c^4 - a*b^5 + 11*a*b^4*c - 10*a*b^3*c^2 - 10*a*b^2*c^3 + 11*a*b*c^4 - a*c^5 + b^6 - b^5*c - 5*b^4*c^2 + 10*b^3*c^3 - 5*b^2*c^4 - b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^4 * (b - a)^2 + (1 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^4 * (c - b)^2 + (8 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (18 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (18 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (24 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^4 + (5 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 - a^5*b - a^5*c - 5*a^4*b^2 + 11*a^4*b*c - 5*a^4*c^2 + 10*a^3*b^3 - 10*a^3*b^2*c - 10*a^3*b*c^2 + 10*a^3*c^3 - 5*a^2*b^4 - 10*a^2*b^3*c + 30*a^2*b^2*c^2 - 10*a^2*b*c^3 - 5*a^2*c^4 - a*b^5 + 11*a*b^4*c - 10*a*b^3*c^2 - 10*a*b^2*c^3 + 11*a*b*c^4 - a*c^5 + b^6 - b^5*c - 5*b^4*c^2 + 10*b^3*c^3 - 5*b^2*c^4 - b*c^5 + c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^4 * (a - b) * (a - c) + b^4 * (b - a) * (b - c) + c^4 * (c - a) * (c - b) ≥ 5 * (b - c)^2 * (c - a)^2 * (a - b)^2) := @solution
#print axioms solution
