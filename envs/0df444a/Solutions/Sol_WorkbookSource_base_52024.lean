-- Prove2me | solution 1 for WorkbookSource.base_52024
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:29.043924+00:00
-- url     : https://prove2.me/submissions/b79e1587-7662-4f24-b6f4-8fac993cb701

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (45 * a + b + 9 * c) / (c + 2 * a) ^ 2 + (45 * b + c + 9 * a) / (a + 2 * b) ^ 2 + (45 * c + a + 9 * b) / (b + 2 * c) ^ 2 ≥ 55 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 56*a^5*b + 188*a^5*c + 73*a^4*b^2 + 452*a^4*b*c - 191*a^4*c^2 - 134*a^3*b^3 - 30*a^3*b^2*c - 426*a^3*b*c^2 - 134*a^3*c^3 - 191*a^2*b^4 - 426*a^2*b^3*c + 24*a^2*b^2*c^2 - 30*a^2*b*c^3 + 73*a^2*c^4 + 188*a*b^5 + 452*a*b^4*c - 30*a*b^3*c^2 - 426*a*b^2*c^3 + 452*a*b*c^4 + 56*a*c^5 + 4*b^6 + 56*b^5*c + 73*b^4*c^2 - 134*b^3*c^3 - 191*b^2*c^4 + 188*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1782 : ℝ) * a^4 * (b - a)^2 + (1782 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1782 : ℝ) * a^4 * (c - b)^2 + (3996 : ℝ) * a^3 * (b - a)^3 + (5400 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (7668 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (3132 : ℝ) * a^3 * (c - b)^3 + (2910 : ℝ) * a^2 * (b - a)^4 + (4632 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (9054 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (7332 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1614 : ℝ) * a^2 * (c - b)^4 + (692 : ℝ) * a^1 * (b - a)^5 + (1202 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (3824 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (5128 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2350 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (268 : ℝ) * a^1 * (c - b)^5 + (465 : ℝ) * (b - a)^4 * (c - b)^2 + (1062 : ℝ) * (b - a)^3 * (c - b)^3 + (809 : ℝ) * (b - a)^2 * (c - b)^4 + (212 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6 + 56*a^5*b + 188*a^5*c + 73*a^4*b^2 + 452*a^4*b*c - 191*a^4*c^2 - 134*a^3*b^3 - 30*a^3*b^2*c - 426*a^3*b*c^2 - 134*a^3*c^3 - 191*a^2*b^4 - 426*a^2*b^3*c + 24*a^2*b^2*c^2 - 30*a^2*b*c^3 + 73*a^2*c^4 + 188*a*b^5 + 452*a*b^4*c - 30*a*b^3*c^2 - 426*a*b^2*c^3 + 452*a*b*c^4 + 56*a*c^5 + 4*b^6 + 56*b^5*c + 73*b^4*c^2 - 134*b^3*c^3 - 191*b^2*c^4 + 188*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1782 : ℝ) * a^4 * (c - a)^2 + (1782 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1782 : ℝ) * a^4 * (b - c)^2 + (3996 : ℝ) * a^3 * (c - a)^3 + (6588 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (8856 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (3132 : ℝ) * a^3 * (b - c)^3 + (2910 : ℝ) * a^2 * (c - a)^4 + (7008 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (12618 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (8520 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1614 : ℝ) * a^2 * (b - c)^4 + (692 : ℝ) * a^1 * (c - a)^5 + (2258 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (5936 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (6052 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2218 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (268 : ℝ) * a^1 * (b - c)^5 + (465 : ℝ) * (c - a)^4 * (b - c)^2 + (798 : ℝ) * (c - a)^3 * (b - c)^3 + (413 : ℝ) * (c - a)^2 * (b - c)^4 + (80 : ℝ) * (c - a)^1 * (b - c)^5 + (4 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 56*a^5*b + 188*a^5*c + 73*a^4*b^2 + 452*a^4*b*c - 191*a^4*c^2 - 134*a^3*b^3 - 30*a^3*b^2*c - 426*a^3*b*c^2 - 134*a^3*c^3 - 191*a^2*b^4 - 426*a^2*b^3*c + 24*a^2*b^2*c^2 - 30*a^2*b*c^3 + 73*a^2*c^4 + 188*a*b^5 + 452*a*b^4*c - 30*a*b^3*c^2 - 426*a*b^2*c^3 + 452*a*b*c^4 + 56*a*c^5 + 4*b^6 + 56*b^5*c + 73*b^4*c^2 - 134*b^3*c^3 - 191*b^2*c^4 + 188*b*c^5 + 4*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (4*a^6 + 56*a^5*b + 188*a^5*c + 73*a^4*b^2 + 452*a^4*b*c - 191*a^4*c^2 - 134*a^3*b^3 - 30*a^3*b^2*c - 426*a^3*b*c^2 - 134*a^3*c^3 - 191*a^2*b^4 - 426*a^2*b^3*c + 24*a^2*b^2*c^2 - 30*a^2*b*c^3 + 73*a^2*c^4 + 188*a*b^5 + 452*a*b^4*c - 30*a*b^3*c^2 - 426*a*b^2*c^3 + 452*a*b*c^4 + 56*a*c^5 + 4*b^6 + 56*b^5*c + 73*b^4*c^2 - 134*b^3*c^3 - 191*b^2*c^4 + 188*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (45 * a + b + 9 * c) / (c + 2 * a) ^ 2 + (45 * b + c + 9 * a) / (a + 2 * b) ^ 2 + (45 * c + a + 9 * b) / (b + 2 * c) ^ 2 ≥ 55 / (a + b + c)) := @solution
#print axioms solution
