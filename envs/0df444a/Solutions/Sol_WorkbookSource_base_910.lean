-- Prove2me | solution 1 for WorkbookSource.base_910
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:22.933049+00:00
-- url     : https://prove2.me/submissions/07b03377-fb96-464c-a15d-9c9a3a0edc25

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (1 - 2 * c^2 / (a + b)^2) + b * c * (1 - 2 * a^2 / (b + c)^2) + c * a * (1 - 2 * b^2 / (c + a)^2) ≤ (1 / 2) * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2 + 6*a^6*b*c + a^6*c^2 + 8*a^5*b^2*c + 8*a^5*b*c^2 - 2*a^4*b^4 - 6*a^4*b^3*c - 6*a^4*b*c^3 - 2*a^4*c^4 - 6*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 - 6*a^3*b*c^4 + a^2*b^6 + 8*a^2*b^5*c - 10*a^2*b^3*c^3 + 8*a^2*b*c^5 + a^2*c^6 + 6*a*b^6*c + 8*a*b^5*c^2 - 6*a*b^4*c^3 - 6*a*b^3*c^4 + 8*a*b^2*c^5 + 6*a*b*c^6 + b^6*c^2 - 2*b^4*c^4 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (b - a)^2 + (96 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^6 * (c - b)^2 + (352 : ℝ) * a^5 * (b - a)^3 + (528 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (624 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (224 : ℝ) * a^5 * (c - b)^3 + (504 : ℝ) * a^4 * (b - a)^4 + (1008 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1432 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (928 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (184 : ℝ) * a^4 * (c - b)^4 + (352 : ℝ) * a^3 * (b - a)^5 + (880 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1504 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1376 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (528 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (64 : ℝ) * a^3 * (c - b)^5 + (120 : ℝ) * a^2 * (b - a)^6 + (360 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (745 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (890 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (505 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (120 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (8 : ℝ) * a^2 * (c - b)^6 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (148 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (230 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (176 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (62 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^6 * (c - b)^2 + (12 : ℝ) * (b - a)^5 * (c - b)^3 + (13 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2 + 6*a^6*b*c + a^6*c^2 + 8*a^5*b^2*c + 8*a^5*b*c^2 - 2*a^4*b^4 - 6*a^4*b^3*c - 6*a^4*b*c^3 - 2*a^4*c^4 - 6*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 - 6*a^3*b*c^4 + a^2*b^6 + 8*a^2*b^5*c - 10*a^2*b^3*c^3 + 8*a^2*b*c^5 + a^2*c^6 + 6*a*b^6*c + 8*a*b^5*c^2 - 6*a*b^4*c^3 - 6*a*b^3*c^4 + 8*a*b^2*c^5 + 6*a*b*c^6 + b^6*c^2 - 2*b^4*c^4 + b^2*c^6) := by
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
  have hn : 0 ≤ ((a + b + c)*(a^5*b^2 + 6*a^5*b*c + a^5*c^2 - a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 6*a^3*b^3*c - 2*a^3*b^2*c^2 - 6*a^3*b*c^3 - a^3*c^4 + a^2*b^5 + a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a^2*b*c^4 + a^2*c^5 + 6*a*b^5*c + a*b^4*c^2 - 6*a*b^3*c^3 + a*b^2*c^4 + 6*a*b*c^5 + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b * (1 - 2 * c^2 / (a + b)^2) + b * c * (1 - 2 * a^2 / (b + c)^2) + c * a * (1 - 2 * b^2 / (c + a)^2) ≤ (1 / 2) * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
