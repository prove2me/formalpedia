-- Prove2me | solution 1 for WorkbookSource.base_55767
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:14.950567+00:00
-- url     : https://prove2.me/submissions/86dc5818-d16a-4410-b91f-ea1403a6cba4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a + b + c) * (a * b + b * c + c * a)) / (9 * a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b^2 + 12*a^4*b*c + 8*a^4*c^2 + 12*a^3*b^3 + a^3*b^2*c - 22*a^3*b*c^2 + 12*a^3*c^3 + 8*a^2*b^4 - 22*a^2*b^3*c - 45*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + 12*a*b^4*c + a*b^3*c^2 - 22*a*b^2*c^3 + 12*a*b*c^4 + 4*b^4*c^2 + 12*b^3*c^3 + 8*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (99 : ℝ) * a^4 * (b - a)^2 + (99 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (99 : ℝ) * a^4 * (c - b)^2 + (297 : ℝ) * a^3 * (b - a)^3 + (450 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (351 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (99 : ℝ) * a^3 * (c - b)^3 + (321 : ℝ) * a^2 * (b - a)^4 + (651 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (531 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (201 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^2 * (c - b)^4 + (147 : ℝ) * a^1 * (b - a)^5 + (376 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (359 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (158 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (28 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * (b - a)^6 + (76 : ℝ) * (b - a)^5 * (c - b)^1 + (88 : ℝ) * (b - a)^4 * (c - b)^2 + (44 : ℝ) * (b - a)^3 * (c - b)^3 + (8 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*b^2 + 12*a^4*b*c + 8*a^4*c^2 + 12*a^3*b^3 + a^3*b^2*c - 22*a^3*b*c^2 + 12*a^3*c^3 + 8*a^2*b^4 - 22*a^2*b^3*c - 45*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + 12*a*b^4*c + a*b^3*c^2 - 22*a*b^2*c^3 + 12*a*b*c^4 + 4*b^4*c^2 + 12*b^3*c^3 + 8*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (99 : ℝ) * a^4 * (c - a)^2 + (99 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (99 : ℝ) * a^4 * (b - c)^2 + (297 : ℝ) * a^3 * (c - a)^3 + (441 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (342 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (99 : ℝ) * a^3 * (b - c)^3 + (321 : ℝ) * a^2 * (c - a)^4 + (633 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (504 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (192 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (24 : ℝ) * a^2 * (b - c)^4 + (147 : ℝ) * a^1 * (c - a)^5 + (359 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (325 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (133 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (24 : ℝ) * (c - a)^6 + (68 : ℝ) * (c - a)^5 * (b - c)^1 + (68 : ℝ) * (c - a)^4 * (b - c)^2 + (28 : ℝ) * (c - a)^3 * (b - c)^3 + (4 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b^2 + 12*a^4*b*c + 8*a^4*c^2 + 12*a^3*b^3 + a^3*b^2*c - 22*a^3*b*c^2 + 12*a^3*c^3 + 8*a^2*b^4 - 22*a^2*b^3*c - 45*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + 12*a*b^4*c + a*b^3*c^2 - 22*a*b^2*c^3 + 12*a*b*c^4 + 4*b^4*c^2 + 12*b^3*c^3 + 8*b^2*c^4) := by
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
  have hn : 0 ≤ (4*a^4*b^2 + 12*a^4*b*c + 8*a^4*c^2 + 12*a^3*b^3 + a^3*b^2*c - 22*a^3*b*c^2 + 12*a^3*c^3 + 8*a^2*b^4 - 22*a^2*b^3*c - 45*a^2*b^2*c^2 + a^2*b*c^3 + 4*a^2*c^4 + 12*a*b^4*c + a*b^3*c^2 - 22*a*b^2*c^3 + 12*a*b*c^4 + 4*b^4*c^2 + 12*b^3*c^3 + 8*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a + b + c) * (a * b + b * c + c * a)) / (9 * a * b * c)) := @solution
#print axioms solution
