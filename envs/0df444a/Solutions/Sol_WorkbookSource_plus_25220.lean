-- Prove2me | solution 1 for WorkbookSource.plus_25220
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:06.909225+00:00
-- url     : https://prove2.me/submissions/bda3c558-e33b-4f65-a466-cf0de39dd5c1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / a + (c + a) / b ≥ 2 * a / (b + c) + (b + c) / (a + b) + (b + c) / (a + c) + 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (14 : ℝ) * a^4 * (c - b)^2 + (38 : ℝ) * a^3 * (b - a)^3 + (57 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (13 : ℝ) * a^3 * (c - b)^3 + (44 : ℝ) * a^2 * (b - a)^4 + (88 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (69 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (25 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^2 * (c - b)^4 + (22 : ℝ) * a^1 * (b - a)^5 + (55 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (50 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * b^4 * (a - b)^2 + (16 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (14 : ℝ) * b^4 * (c - a)^2 + (43 : ℝ) * b^3 * (a - b)^3 + (70 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (50 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (13 : ℝ) * b^3 * (c - a)^3 + (48 : ℝ) * b^2 * (a - b)^4 + (101 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (78 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (26 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (3 : ℝ) * b^2 * (c - a)^4 + (23 : ℝ) * b^1 * (a - b)^5 + (59 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (54 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (21 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (3 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (4 : ℝ) * (a - b)^6 + (12 : ℝ) * (a - b)^5 * (c - a)^1 + (13 : ℝ) * (a - b)^4 * (c - a)^2 + (6 : ℝ) * (a - b)^3 * (c - a)^3 + (1 : ℝ) * (a - b)^2 * (c - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * b^4 * (c - b)^2 + (12 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (12 : ℝ) * b^4 * (a - c)^2 + (43 : ℝ) * b^3 * (c - b)^3 + (59 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (39 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (10 : ℝ) * b^3 * (a - c)^3 + (48 : ℝ) * b^2 * (c - b)^4 + (91 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (63 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (19 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (2 : ℝ) * b^2 * (a - c)^4 + (23 : ℝ) * b^1 * (c - b)^5 + (56 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (48 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (17 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * (c - b)^6 + (12 : ℝ) * (c - b)^5 * (a - c)^1 + (13 : ℝ) * (c - b)^4 * (a - c)^2 + (6 : ℝ) * (c - b)^3 * (a - c)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / c + (b + c) / a + (c + a) / b ≥ 2 * a / (b + c) + (b + c) / (a + b) + (b + c) / (a + c) + 3) := @solution
#print axioms solution
