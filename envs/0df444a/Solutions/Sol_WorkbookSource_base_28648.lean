-- Prove2me | solution 1 for WorkbookSource.base_28648
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:03:55.432765+00:00
-- url     : https://prove2.me/submissions/c22d932d-3423-4235-9c85-b86a661c3c28

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c)) ≥ 9 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6 + 22*a^5*b + 22*a^5*c + 7*a^4*b^2 + 30*a^4*b*c + 7*a^4*c^2 - 14*a^3*b^3 - 30*a^3*b^2*c - 30*a^3*b*c^2 - 14*a^3*c^3 + 7*a^2*b^4 - 30*a^2*b^3*c - 66*a^2*b^2*c^2 - 30*a^2*b*c^3 + 7*a^2*c^4 + 22*a*b^5 + 30*a*b^4*c - 30*a*b^3*c^2 - 30*a*b^2*c^3 + 30*a*b*c^4 + 22*a*c^5 + 8*b^6 + 22*b^5*c + 7*b^4*c^2 - 14*b^3*c^3 + 7*b^2*c^4 + 22*b*c^5 + 8*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (448 : ℝ) * a^4 * (b - a)^2 + (448 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (448 : ℝ) * a^4 * (c - b)^2 + (1104 : ℝ) * a^3 * (b - a)^3 + (1656 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1928 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (688 : ℝ) * a^3 * (c - b)^3 + (1008 : ℝ) * a^2 * (b - a)^4 + (2016 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2808 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1800 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (384 : ℝ) * a^2 * (c - b)^4 + (404 : ℝ) * a^1 * (b - a)^5 + (1010 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1668 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1492 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (614 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (92 : ℝ) * a^1 * (c - b)^5 + (60 : ℝ) * (b - a)^6 + (180 : ℝ) * (b - a)^5 * (c - b)^1 + (347 : ℝ) * (b - a)^4 * (c - b)^2 + (394 : ℝ) * (b - a)^3 * (c - b)^3 + (237 : ℝ) * (b - a)^2 * (c - b)^4 + (70 : ℝ) * (b - a)^1 * (c - b)^5 + (8 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6 + 22*a^5*b + 22*a^5*c + 7*a^4*b^2 + 30*a^4*b*c + 7*a^4*c^2 - 14*a^3*b^3 - 30*a^3*b^2*c - 30*a^3*b*c^2 - 14*a^3*c^3 + 7*a^2*b^4 - 30*a^2*b^3*c - 66*a^2*b^2*c^2 - 30*a^2*b*c^3 + 7*a^2*c^4 + 22*a*b^5 + 30*a*b^4*c - 30*a*b^3*c^2 - 30*a*b^2*c^3 + 30*a*b*c^4 + 22*a*c^5 + 8*b^6 + 22*b^5*c + 7*b^4*c^2 - 14*b^3*c^3 + 7*b^2*c^4 + 22*b*c^5 + 8*c^6) := by
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
  have hn : 0 ≤ (8*a^6 + 22*a^5*b + 22*a^5*c + 7*a^4*b^2 + 30*a^4*b*c + 7*a^4*c^2 - 14*a^3*b^3 - 30*a^3*b^2*c - 30*a^3*b*c^2 - 14*a^3*c^3 + 7*a^2*b^4 - 30*a^2*b^3*c - 66*a^2*b^2*c^2 - 30*a^2*b*c^3 + 7*a^2*c^4 + 22*a*b^5 + 30*a*b^4*c - 30*a*b^3*c^2 - 30*a*b^2*c^3 + 30*a*b*c^4 + 22*a*c^5 + 8*b^6 + 22*b^5*c + 7*b^4*c^2 - 14*b^3*c^3 + 7*b^2*c^4 + 22*b*c^5 + 8*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b) + a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c)) ≥ 9 / 4) := @solution
#print axioms solution
