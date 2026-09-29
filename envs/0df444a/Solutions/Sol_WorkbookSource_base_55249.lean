-- Prove2me | solution 1 for WorkbookSource.base_55249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:51.850874+00:00
-- url     : https://prove2.me/submissions/ba27f185-6423-4b4f-b281-36e96851719b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + c) / (2 * a + b + c) + (2 * b + a) / (2 * b + c + a) + (2 * c + b) / (2 * c + a + b) ≥ 2 + 1 / 4 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b + 6*a^4*c + a^3*b^2 + 12*a^3*b*c - 3*a^3*c^2 - 3*a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 + a^2*c^3 + 6*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 2*a*c^4 + 2*b^4*c + b^3*c^2 - 3*b^2*c^3 + 6*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^3 * (b - a)^2 + (40 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^3 * (c - b)^2 + (78 : ℝ) * a^2 * (b - a)^3 + (123 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (129 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^2 * (c - b)^3 + (44 : ℝ) * a^1 * (b - a)^4 + (96 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (114 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (62 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^5 + (19 : ℝ) * (b - a)^4 * (c - b)^1 + (28 : ℝ) * (b - a)^3 * (c - b)^2 + (21 : ℝ) * (b - a)^2 * (c - b)^3 + (6 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b + 6*a^4*c + a^3*b^2 + 12*a^3*b*c - 3*a^3*c^2 - 3*a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 + a^2*c^3 + 6*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 2*a*c^4 + 2*b^4*c + b^3*c^2 - 3*b^2*c^3 + 6*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^3 * (c - a)^2 + (40 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (40 : ℝ) * a^3 * (b - c)^2 + (78 : ℝ) * a^2 * (c - a)^3 + (111 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (117 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (42 : ℝ) * a^2 * (b - c)^3 + (44 : ℝ) * a^1 * (c - a)^4 + (80 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (90 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (54 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (8 : ℝ) * a^1 * (b - c)^4 + (6 : ℝ) * (c - a)^5 + (11 : ℝ) * (c - a)^4 * (b - c)^1 + (12 : ℝ) * (c - a)^3 * (b - c)^2 + (9 : ℝ) * (c - a)^2 * (b - c)^3 + (2 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b + 6*a^4*c + a^3*b^2 + 12*a^3*b*c - 3*a^3*c^2 - 3*a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 + a^2*c^3 + 6*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 2*a*c^4 + 2*b^4*c + b^3*c^2 - 3*b^2*c^3 + 6*b*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b + 6*a^4*c + a^3*b^2 + 12*a^3*b*c - 3*a^3*c^2 - 3*a^2*b^3 - 18*a^2*b^2*c - 18*a^2*b*c^2 + a^2*c^3 + 6*a*b^4 + 12*a*b^3*c - 18*a*b^2*c^2 + 12*a*b*c^3 + 2*a*c^4 + 2*b^4*c + b^3*c^2 - 3*b^2*c^3 + 6*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a + c) / (2 * a + b + c) + (2 * b + a) / (2 * b + c + a) + (2 * c + b) / (2 * c + a + b) ≥ 2 + 1 / 4 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
