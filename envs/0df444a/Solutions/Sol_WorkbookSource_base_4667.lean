-- Prove2me | solution 1 for WorkbookSource.base_4667
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:27.964981+00:00
-- url     : https://prove2.me/submissions/4357bd6f-a9be-44d3-9bbe-37c09ecf5578

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (1 + a * b * c) ≥ a / (1 + a ^ 2 * b) + b / (1 + b ^ 2 * c) + c / (1 + c ^ 2 * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c^2 - a^3*b^2*c^2 + a^3*b + a^2*b^4*c - a^2*b^3*c^2 - a^2*b^2*c^3 - a^2*b*c + a*b^2*c^4 - a*b^2*c - a*b*c^2 + a*c^3 + b^3*c) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^5 * (b - a)^2 + (2 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^5 * (c - b)^2 + (7 : ℝ) * a^4 * (b - a)^3 + (12 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (11 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^4 * (c - b)^3 + (9 : ℝ) * a^3 * (b - a)^4 + (22 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (23 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (10 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^3 * (c - b)^4 + (5 : ℝ) * a^2 * (b - a)^5 + (16 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (20 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (11 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^2 * (b - a)^2 + (2 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^2 * (c - b)^2 + (1 : ℝ) * a^1 * (b - a)^6 + (4 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (6 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^3 + (1 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (1 : ℝ) * a^1 * (c - b)^3 + (1 : ℝ) * (b - a)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^1 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c^2 - a^3*b^2*c^2 + a^3*b + a^2*b^4*c - a^2*b^3*c^2 - a^2*b^2*c^3 - a^2*b*c + a*b^2*c^4 - a*b^2*c - a*b*c^2 + a*c^3 + b^3*c) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^5 * (c - a)^2 + (2 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^5 * (b - c)^2 + (7 : ℝ) * a^4 * (c - a)^3 + (9 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^4 * (b - c)^3 + (9 : ℝ) * a^3 * (c - a)^4 + (14 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (11 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (6 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^3 * (b - c)^4 + (5 : ℝ) * a^2 * (c - a)^5 + (9 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (6 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (3 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^2 * (c - a)^2 + (1 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^2 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^6 + (2 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (1 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (3 : ℝ) * a^1 * (c - a)^3 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (1 : ℝ) * a^1 * (b - c)^3 + (1 : ℝ) * (c - a)^4 + (3 : ℝ) * (c - a)^3 * (b - c)^1 + (3 : ℝ) * (c - a)^2 * (b - c)^2 + (1 : ℝ) * (c - a)^1 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c^2 - a^3*b^2*c^2 + a^3*b + a^2*b^4*c - a^2*b^3*c^2 - a^2*b^2*c^3 - a^2*b*c + a*b^2*c^4 - a*b^2*c - a*b*c^2 + a*c^3 + b^3*c) := by
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
  have hn : 0 ≤ (a^4*b*c^2 - a^3*b^2*c^2 + a^3*b + a^2*b^4*c - a^2*b^3*c^2 - a^2*b^2*c^3 - a^2*b*c + a*b^2*c^4 - a*b^2*c - a*b*c^2 + a*c^3 + b^3*c) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) / (1 + a * b * c) ≥ a / (1 + a ^ 2 * b) + b / (1 + b ^ 2 * c) + c / (1 + c ^ 2 * a)) := @solution
#print axioms solution
