-- Prove2me | solution 1 for WorkbookSource.base_21045
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:08.063853+00:00
-- url     : https://prove2.me/submissions/aca49eb9-b2aa-4909-9253-8481e005cf4c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 3 / 5 ≤ a ^ 2 / (a ^ 2 + (b + c) ^ 2) + b ^ 2 / (b ^ 2 + (c + a) ^ 2) + c ^ 2 / (c ^ 2 + (a + b) ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 + 4*a^5*b + 4*a^5*c + 6*a^4*b^2 + 2*a^4*b*c + 6*a^4*c^2 + 8*a^3*b^3 - 14*a^3*b^2*c - 14*a^3*b*c^2 + 8*a^3*c^3 + 6*a^2*b^4 - 14*a^2*b^3*c - 12*a^2*b^2*c^2 - 14*a^2*b*c^3 + 6*a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 14*a*b^3*c^2 - 14*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 2*b^6 + 4*b^5*c + 6*b^4*c^2 + 8*b^3*c^3 + 6*b^2*c^4 + 4*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (130 : ℝ) * a^4 * (b - a)^2 + (130 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (130 : ℝ) * a^4 * (c - b)^2 + (356 : ℝ) * a^3 * (b - a)^3 + (534 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (506 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (164 : ℝ) * a^3 * (c - b)^3 + (372 : ℝ) * a^2 * (b - a)^4 + (744 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (786 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (414 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (84 : ℝ) * a^2 * (c - b)^4 + (176 : ℝ) * a^1 * (b - a)^5 + (440 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (540 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (370 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (134 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (20 : ℝ) * a^1 * (c - b)^5 + (32 : ℝ) * (b - a)^6 + (96 : ℝ) * (b - a)^5 * (c - b)^1 + (136 : ℝ) * (b - a)^4 * (c - b)^2 + (112 : ℝ) * (b - a)^3 * (c - b)^3 + (56 : ℝ) * (b - a)^2 * (c - b)^4 + (16 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 + 4*a^5*b + 4*a^5*c + 6*a^4*b^2 + 2*a^4*b*c + 6*a^4*c^2 + 8*a^3*b^3 - 14*a^3*b^2*c - 14*a^3*b*c^2 + 8*a^3*c^3 + 6*a^2*b^4 - 14*a^2*b^3*c - 12*a^2*b^2*c^2 - 14*a^2*b*c^3 + 6*a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 14*a*b^3*c^2 - 14*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 2*b^6 + 4*b^5*c + 6*b^4*c^2 + 8*b^3*c^3 + 6*b^2*c^4 + 4*b*c^5 + 2*c^6) := by
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
  have hn : 0 ≤ (2*a^6 + 4*a^5*b + 4*a^5*c + 6*a^4*b^2 + 2*a^4*b*c + 6*a^4*c^2 + 8*a^3*b^3 - 14*a^3*b^2*c - 14*a^3*b*c^2 + 8*a^3*c^3 + 6*a^2*b^4 - 14*a^2*b^3*c - 12*a^2*b^2*c^2 - 14*a^2*b*c^3 + 6*a^2*c^4 + 4*a*b^5 + 2*a*b^4*c - 14*a*b^3*c^2 - 14*a*b^2*c^3 + 2*a*b*c^4 + 4*a*c^5 + 2*b^6 + 4*b^5*c + 6*b^4*c^2 + 8*b^3*c^3 + 6*b^2*c^4 + 4*b*c^5 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), 3 / 5 ≤ a ^ 2 / (a ^ 2 + (b + c) ^ 2) + b ^ 2 / (b ^ 2 + (c + a) ^ 2) + c ^ 2 / (c ^ 2 + (a + b) ^ 2)) := @solution
#print axioms solution
