-- Prove2me | solution 1 for WorkbookSource.plus_36102
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:29.154193+00:00
-- url     : https://prove2.me/submissions/082ab658-b668-4444-b9b7-3afe48d4c74c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) + (2 * (a * b + b * c + c * a)) / (a^2 + b^2 + c^2) + (a + b + c)^2 / (3 * (a^2 + b^2 + c^2)) + (3 * (a * b + b * c + c * a)) / (a + b + c)^2 ≥ 5   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c + 2*a^5*b^2 - 12*a^5*b*c + 2*a^5*c^2 + 3*a^4*b^3 - 9*a^4*b^2*c - 9*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - 8*a^3*b^3*c + 23*a^3*b^2*c^2 - 8*a^3*b*c^3 + 3*a^3*c^4 + 2*a^2*b^5 - 9*a^2*b^4*c + 23*a^2*b^3*c^2 + 23*a^2*b^2*c^3 - 9*a^2*b*c^4 + 2*a^2*c^5 + 2*a*b^6 - 12*a*b^5*c - 9*a*b^4*c^2 - 8*a*b^3*c^3 - 9*a*b^2*c^4 - 12*a*b*c^5 + 2*a*c^6 + b^7 + 2*b^6*c + 2*b^5*c^2 + 3*b^4*c^3 + 3*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (43 : ℝ) * a^3 * (b - a)^4 + (86 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (129 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (86 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (43 : ℝ) * a^3 * (c - b)^4 + (92 : ℝ) * a^2 * (b - a)^5 + (230 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (350 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (295 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (157 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (37 : ℝ) * a^2 * (c - b)^5 + (66 : ℝ) * a^1 * (b - a)^6 + (198 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (323 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (316 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (195 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (70 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (11 : ℝ) * a^1 * (c - b)^6 + (16 : ℝ) * (b - a)^7 + (56 : ℝ) * (b - a)^6 * (c - b)^1 + (100 : ℝ) * (b - a)^5 * (c - b)^2 + (110 : ℝ) * (b - a)^4 * (c - b)^3 + (78 : ℝ) * (b - a)^3 * (c - b)^4 + (35 : ℝ) * (b - a)^2 * (c - b)^5 + (9 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c + 2*a^5*b^2 - 12*a^5*b*c + 2*a^5*c^2 + 3*a^4*b^3 - 9*a^4*b^2*c - 9*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - 8*a^3*b^3*c + 23*a^3*b^2*c^2 - 8*a^3*b*c^3 + 3*a^3*c^4 + 2*a^2*b^5 - 9*a^2*b^4*c + 23*a^2*b^3*c^2 + 23*a^2*b^2*c^3 - 9*a^2*b*c^4 + 2*a^2*c^5 + 2*a*b^6 - 12*a*b^5*c - 9*a*b^4*c^2 - 8*a*b^3*c^3 - 9*a*b^2*c^4 - 12*a*b*c^5 + 2*a*c^6 + b^7 + 2*b^6*c + 2*b^5*c^2 + 3*b^4*c^3 + 3*b^3*c^4 + 2*b^2*c^5 + 2*b*c^6 + c^7) := by
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
  have hn : 0 ≤ ((a^2 - a*b - a*c + b^2 - b*c + c^2)*(a^5 + 3*a^4*b + 3*a^4*c + 4*a^3*b^2 - 5*a^3*b*c + 4*a^3*c^2 + 4*a^2*b^3 - 10*a^2*b^2*c - 10*a^2*b*c^2 + 4*a^2*c^3 + 3*a*b^4 - 5*a*b^3*c - 10*a*b^2*c^2 - 5*a*b*c^3 + 3*a*c^4 + b^5 + 3*b^4*c + 4*b^3*c^2 + 4*b^2*c^3 + 3*b*c^4 + c^5)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3) / (3 * a * b * c) + (2 * (a * b + b * c + c * a)) / (a^2 + b^2 + c^2) + (a + b + c)^2 / (3 * (a^2 + b^2 + c^2)) + (3 * (a * b + b * c + c * a)) / (a + b + c)^2 ≥ 5) := @solution
#print axioms solution
