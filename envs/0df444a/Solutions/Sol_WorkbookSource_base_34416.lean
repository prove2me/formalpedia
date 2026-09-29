-- Prove2me | solution 1 for WorkbookSource.base_34416
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:23.819423+00:00
-- url     : https://prove2.me/submissions/3fc9603c-7dad-46ca-a3f1-373d3342cc02

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^6 + 4*a^5*b + 4*a^5*c + 36*a^4*b^2 - 28*a^4*b*c + 36*a^4*c^2 + 8*a^3*b^3 - 64*a^3*b^2*c + 16*a^3*b*c^2 + 8*a^3*c^3 + 36*a^2*b^4 + 16*a^2*b^3*c - 72*a^2*b^2*c^2 - 64*a^2*b*c^3 + 36*a^2*c^4 + 4*a*b^5 - 28*a*b^4*c - 64*a*b^3*c^2 + 16*a*b^2*c^3 - 28*a*b*c^4 + 4*a*c^5 + 12*b^6 + 4*b^5*c + 36*b^4*c^2 + 8*b^3*c^3 + 36*b^2*c^4 + 4*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (380 : ℝ) * a^4 * (b - a)^2 + (380 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (380 : ℝ) * a^4 * (c - b)^2 + (1056 : ℝ) * a^3 * (b - a)^3 + (1624 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1496 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (464 : ℝ) * a^3 * (c - b)^3 + (1152 : ℝ) * a^2 * (b - a)^4 + (2384 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2496 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1264 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (264 : ℝ) * a^2 * (c - b)^4 + (576 : ℝ) * a^1 * (b - a)^5 + (1480 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1840 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1240 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (464 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (80 : ℝ) * a^1 * (c - b)^5 + (112 : ℝ) * (b - a)^6 + (336 : ℝ) * (b - a)^5 * (c - b)^1 + (496 : ℝ) * (b - a)^4 * (c - b)^2 + (432 : ℝ) * (b - a)^3 * (c - b)^3 + (236 : ℝ) * (b - a)^2 * (c - b)^4 + (76 : ℝ) * (b - a)^1 * (c - b)^5 + (12 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^6 + 4*a^5*b + 4*a^5*c + 36*a^4*b^2 - 28*a^4*b*c + 36*a^4*c^2 + 8*a^3*b^3 - 64*a^3*b^2*c + 16*a^3*b*c^2 + 8*a^3*c^3 + 36*a^2*b^4 + 16*a^2*b^3*c - 72*a^2*b^2*c^2 - 64*a^2*b*c^3 + 36*a^2*c^4 + 4*a*b^5 - 28*a*b^4*c - 64*a*b^3*c^2 + 16*a*b^2*c^3 - 28*a*b*c^4 + 4*a*c^5 + 12*b^6 + 4*b^5*c + 36*b^4*c^2 + 8*b^3*c^3 + 36*b^2*c^4 + 4*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (380 : ℝ) * a^4 * (c - a)^2 + (380 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (380 : ℝ) * a^4 * (b - c)^2 + (1056 : ℝ) * a^3 * (c - a)^3 + (1544 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1416 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (464 : ℝ) * a^3 * (b - c)^3 + (1152 : ℝ) * a^2 * (c - a)^4 + (2224 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (2256 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1184 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (264 : ℝ) * a^2 * (b - c)^4 + (576 : ℝ) * a^1 * (c - a)^5 + (1400 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1680 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1160 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (464 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (80 : ℝ) * a^1 * (b - c)^5 + (112 : ℝ) * (c - a)^6 + (336 : ℝ) * (c - a)^5 * (b - c)^1 + (496 : ℝ) * (c - a)^4 * (b - c)^2 + (432 : ℝ) * (c - a)^3 * (b - c)^3 + (236 : ℝ) * (c - a)^2 * (b - c)^4 + (76 : ℝ) * (c - a)^1 * (b - c)^5 + (12 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^6 + 4*a^5*b + 4*a^5*c + 36*a^4*b^2 - 28*a^4*b*c + 36*a^4*c^2 + 8*a^3*b^3 - 64*a^3*b^2*c + 16*a^3*b*c^2 + 8*a^3*c^3 + 36*a^2*b^4 + 16*a^2*b^3*c - 72*a^2*b^2*c^2 - 64*a^2*b*c^3 + 36*a^2*c^4 + 4*a*b^5 - 28*a*b^4*c - 64*a*b^3*c^2 + 16*a*b^2*c^3 - 28*a*b*c^4 + 4*a*c^5 + 12*b^6 + 4*b^5*c + 36*b^4*c^2 + 8*b^3*c^3 + 36*b^2*c^4 + 4*b*c^5 + 12*c^6) := by
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
  have hn : 0 ≤ (12*a^6 + 4*a^5*b + 4*a^5*c + 36*a^4*b^2 - 28*a^4*b*c + 36*a^4*c^2 + 8*a^3*b^3 - 64*a^3*b^2*c + 16*a^3*b*c^2 + 8*a^3*c^3 + 36*a^2*b^4 + 16*a^2*b^3*c - 72*a^2*b^2*c^2 - 64*a^2*b*c^3 + 36*a^2*c^4 + 4*a*b^5 - 28*a*b^4*c - 64*a*b^3*c^2 + 16*a*b^2*c^3 - 28*a*b*c^4 + 4*a*c^5 + 12*b^6 + 4*b^5*c + 36*b^4*c^2 + 8*b^3*c^3 + 36*b^2*c^4 + 4*b*c^5 + 12*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5) := @solution
#print axioms solution
