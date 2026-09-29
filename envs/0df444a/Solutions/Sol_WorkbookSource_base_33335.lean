-- Prove2me | solution 1 for WorkbookSource.base_33335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:29.76373+00:00
-- url     : https://prove2.me/submissions/3f4b0d60-66b9-4723-aabc-fce1d8b232da

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ((c + 2 * a) / b + c / (a + b)) * ((a + 2 * b) / c + a / (b + c)) * ((b + 2 * c) / a + b / (c + a)) ≥ 343 / 8  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (32*a^4*b^2 + 96*a^4*b*c + 64*a^4*c^2 + 96*a^3*b^3 - 87*a^3*b^2*c - 103*a^3*b*c^2 + 96*a^3*c^3 + 64*a^2*b^4 - 103*a^2*b^3*c - 294*a^2*b^2*c^2 - 87*a^2*b*c^3 + 32*a^2*c^4 + 96*a*b^4*c - 87*a*b^3*c^2 - 103*a*b^2*c^3 + 96*a*b*c^4 + 32*b^4*c^2 + 96*b^3*c^3 + 64*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (770 : ℝ) * a^4 * (b - a)^2 + (770 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (770 : ℝ) * a^4 * (c - b)^2 + (2310 : ℝ) * a^3 * (b - a)^3 + (3585 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2815 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (770 : ℝ) * a^3 * (c - b)^3 + (2502 : ℝ) * a^2 * (b - a)^4 + (5244 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4401 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1659 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (192 : ℝ) * a^2 * (c - b)^4 + (1154 : ℝ) * a^1 * (b - a)^5 + (3037 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2996 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1337 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (224 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (192 : ℝ) * (b - a)^6 + (608 : ℝ) * (b - a)^5 * (c - b)^1 + (704 : ℝ) * (b - a)^4 * (c - b)^2 + (352 : ℝ) * (b - a)^3 * (c - b)^3 + (64 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (32*a^4*b^2 + 96*a^4*b*c + 64*a^4*c^2 + 96*a^3*b^3 - 87*a^3*b^2*c - 103*a^3*b*c^2 + 96*a^3*c^3 + 64*a^2*b^4 - 103*a^2*b^3*c - 294*a^2*b^2*c^2 - 87*a^2*b*c^3 + 32*a^2*c^4 + 96*a*b^4*c - 87*a*b^3*c^2 - 103*a*b^2*c^3 + 96*a*b*c^4 + 32*b^4*c^2 + 96*b^3*c^3 + 64*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (770 : ℝ) * a^4 * (c - a)^2 + (770 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (770 : ℝ) * a^4 * (b - c)^2 + (2310 : ℝ) * a^3 * (c - a)^3 + (3345 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (2575 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (770 : ℝ) * a^3 * (b - c)^3 + (2502 : ℝ) * a^2 * (c - a)^4 + (4764 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (3681 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1419 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (192 : ℝ) * a^2 * (b - c)^4 + (1154 : ℝ) * a^1 * (c - a)^5 + (2733 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (2388 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (969 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (160 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (192 : ℝ) * (c - a)^6 + (544 : ℝ) * (c - a)^5 * (b - c)^1 + (544 : ℝ) * (c - a)^4 * (b - c)^2 + (224 : ℝ) * (c - a)^3 * (b - c)^3 + (32 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (32*a^4*b^2 + 96*a^4*b*c + 64*a^4*c^2 + 96*a^3*b^3 - 87*a^3*b^2*c - 103*a^3*b*c^2 + 96*a^3*c^3 + 64*a^2*b^4 - 103*a^2*b^3*c - 294*a^2*b^2*c^2 - 87*a^2*b*c^3 + 32*a^2*c^4 + 96*a*b^4*c - 87*a*b^3*c^2 - 103*a*b^2*c^3 + 96*a*b*c^4 + 32*b^4*c^2 + 96*b^3*c^3 + 64*b^2*c^4) := by
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
  have hn : 0 ≤ (32*a^4*b^2 + 96*a^4*b*c + 64*a^4*c^2 + 96*a^3*b^3 - 87*a^3*b^2*c - 103*a^3*b*c^2 + 96*a^3*c^3 + 64*a^2*b^4 - 103*a^2*b^3*c - 294*a^2*b^2*c^2 - 87*a^2*b*c^3 + 32*a^2*c^4 + 96*a*b^4*c - 87*a*b^3*c^2 - 103*a*b^2*c^3 + 96*a*b*c^4 + 32*b^4*c^2 + 96*b^3*c^3 + 64*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), ((c + 2 * a) / b + c / (a + b)) * ((a + 2 * b) / c + a / (b + c)) * ((b + 2 * c) / a + b / (c + a)) ≥ 343 / 8) := @solution
#print axioms solution
