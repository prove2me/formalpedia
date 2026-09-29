-- Prove2me | solution 1 for WorkbookSource.base_28904
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:33.247653+00:00
-- url     : https://prove2.me/submissions/e42bde9c-8d18-470d-88bb-18fbf3f9fd4e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b) ≤ (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 2*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^3*c - 4*a^2*b*c^3 + 4*a*b^4*c - 4*a*b^3*c^2 - 2*a*b^2*c^3 + 4*a*b*c^4 + 2*b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (34 : ℝ) * a^3 * (b - a)^3 + (52 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (46 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^3 * (c - b)^3 + (34 : ℝ) * a^2 * (b - a)^4 + (70 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (66 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (30 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^5 + (36 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (38 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (b - a)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (6 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 2*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^3*c - 4*a^2*b*c^3 + 4*a*b^4*c - 4*a*b^3*c^2 - 2*a*b^2*c^3 + 4*a*b*c^4 + 2*b^3*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (c - a)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^4 * (b - c)^2 + (34 : ℝ) * a^3 * (c - a)^3 + (50 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (44 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (14 : ℝ) * a^3 * (b - c)^3 + (34 : ℝ) * a^2 * (c - a)^4 + (66 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (60 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (28 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (14 : ℝ) * a^1 * (c - a)^5 + (34 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (34 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (18 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (c - a)^6 + (6 : ℝ) * (c - a)^5 * (b - c)^1 + (6 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 2*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^3*c - 4*a^2*b*c^3 + 4*a*b^4*c - 4*a*b^3*c^2 - 2*a*b^2*c^3 + 4*a*b*c^4 + 2*b^3*c^3) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b) ≤ (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) := @solution
#print axioms solution
