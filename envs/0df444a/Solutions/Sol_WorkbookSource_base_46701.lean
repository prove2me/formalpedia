-- Prove2me | solution 1 for WorkbookSource.base_46701
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:06:11.170496+00:00
-- url     : https://prove2.me/submissions/269f8737-d625-4167-b208-3db5d99b6168

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 7 / 2 - 4 * a * b * c / (b + c) / (c + a) / (a + b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * a^4 * (b - a)^2 + (14 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (14 : ℝ) * a^4 * (c - b)^2 + (42 : ℝ) * a^3 * (b - a)^3 + (71 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (57 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^3 * (c - b)^3 + (46 : ℝ) * a^2 * (b - a)^4 + (108 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (99 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (37 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (22 : ℝ) * a^1 * (b - a)^5 + (65 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (72 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (35 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (14 : ℝ) * (b - a)^5 * (c - b)^1 + (18 : ℝ) * (b - a)^4 * (c - b)^2 + (10 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * a^4 * (c - a)^2 + (14 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (14 : ℝ) * a^4 * (b - c)^2 + (42 : ℝ) * a^3 * (c - a)^3 + (55 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (41 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (14 : ℝ) * a^3 * (b - c)^3 + (46 : ℝ) * a^2 * (c - a)^4 + (76 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (51 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (21 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (22 : ℝ) * a^1 * (c - a)^5 + (45 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (32 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (11 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (10 : ℝ) * (c - a)^5 * (b - c)^1 + (8 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 3*a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + 2*b^3*c^3 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ≥ 7 / 2 - 4 * a * b * c / (b + c) / (c + a) / (a + b)) := @solution
#print axioms solution
