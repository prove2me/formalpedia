-- Prove2me | solution 1 for WorkbookSource.plus_58995
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:28.434676+00:00
-- url     : https://prove2.me/submissions/a50ee583-2496-41a1-9f25-56962a4c9421

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 4 * ((a^2 + b * c) / (b + c) ^ 2 + (b^2 + c * a) / (c + a) ^ 2 + (c^2 + a * b) / (a + b) ^ 2) ≥ 3 + (a + b + c) ^ 2 / (a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^7*b + 4*a^7*c + 7*a^6*b^2 + 18*a^6*b*c + 7*a^6*c^2 - 3*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 - 3*a^5*c^3 - 8*a^4*b^4 - 17*a^4*b^3*c - 6*a^4*b^2*c^2 - 17*a^4*b*c^3 - 8*a^4*c^4 - 3*a^3*b^5 - 17*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 17*a^3*b*c^4 - 3*a^3*c^5 + 7*a^2*b^6 + 11*a^2*b^5*c - 6*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 11*a^2*b*c^5 + 7*a^2*c^6 + 4*a*b^7 + 18*a*b^6*c + 11*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 11*a*b^2*c^5 + 18*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 7*b^6*c^2 - 3*b^5*c^3 - 8*b^4*c^4 - 3*b^3*c^5 + 7*b^2*c^6 + 4*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (320 : ℝ) * a^6 * (b - a)^2 + (320 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (320 : ℝ) * a^6 * (c - b)^2 + (1120 : ℝ) * a^5 * (b - a)^3 + (1680 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (2160 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (800 : ℝ) * a^5 * (c - b)^3 + (1584 : ℝ) * a^4 * (b - a)^4 + (3168 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (5152 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3568 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (784 : ℝ) * a^4 * (c - b)^4 + (1160 : ℝ) * a^3 * (b - a)^5 + (2900 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (5832 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (5848 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2508 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (376 : ℝ) * a^3 * (c - b)^5 + (464 : ℝ) * a^2 * (b - a)^6 + (1392 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (3394 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (4468 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (2830 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (828 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (88 : ℝ) * a^2 * (c - b)^6 + (96 : ℝ) * a^1 * (b - a)^7 + (336 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (976 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1600 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1336 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (572 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (116 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (8 : ℝ) * (b - a)^8 + (32 : ℝ) * (b - a)^7 * (c - b)^1 + (109 : ℝ) * (b - a)^6 * (c - b)^2 + (215 : ℝ) * (b - a)^5 * (c - b)^3 + (222 : ℝ) * (b - a)^4 * (c - b)^4 + (123 : ℝ) * (b - a)^3 * (c - b)^5 + (35 : ℝ) * (b - a)^2 * (c - b)^6 + (4 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^7*b + 4*a^7*c + 7*a^6*b^2 + 18*a^6*b*c + 7*a^6*c^2 - 3*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 - 3*a^5*c^3 - 8*a^4*b^4 - 17*a^4*b^3*c - 6*a^4*b^2*c^2 - 17*a^4*b*c^3 - 8*a^4*c^4 - 3*a^3*b^5 - 17*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 17*a^3*b*c^4 - 3*a^3*c^5 + 7*a^2*b^6 + 11*a^2*b^5*c - 6*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 11*a^2*b*c^5 + 7*a^2*c^6 + 4*a*b^7 + 18*a*b^6*c + 11*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 11*a*b^2*c^5 + 18*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 7*b^6*c^2 - 3*b^5*c^3 - 8*b^4*c^4 - 3*b^3*c^5 + 7*b^2*c^6 + 4*b*c^7) := by
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
  have hn : 0 ≤ (4*a^7*b + 4*a^7*c + 7*a^6*b^2 + 18*a^6*b*c + 7*a^6*c^2 - 3*a^5*b^3 + 11*a^5*b^2*c + 11*a^5*b*c^2 - 3*a^5*c^3 - 8*a^4*b^4 - 17*a^4*b^3*c - 6*a^4*b^2*c^2 - 17*a^4*b*c^3 - 8*a^4*c^4 - 3*a^3*b^5 - 17*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 17*a^3*b*c^4 - 3*a^3*c^5 + 7*a^2*b^6 + 11*a^2*b^5*c - 6*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 11*a^2*b*c^5 + 7*a^2*c^6 + 4*a*b^7 + 18*a*b^6*c + 11*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 11*a*b^2*c^5 + 18*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 7*b^6*c^2 - 3*b^5*c^3 - 8*b^4*c^4 - 3*b^3*c^5 + 7*b^2*c^6 + 4*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), 4 * ((a^2 + b * c) / (b + c) ^ 2 + (b^2 + c * a) / (c + a) ^ 2 + (c^2 + a * b) / (a + b) ^ 2) ≥ 3 + (a + b + c) ^ 2 / (a * b + b * c + c * a)) := @solution
#print axioms solution
