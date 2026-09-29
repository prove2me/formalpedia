-- Prove2me | solution 1 for WorkbookSource.base_26445
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:10:14.90911+00:00
-- url     : https://prove2.me/submissions/f66d483e-e42a-4b40-bcf5-bcd8d1723e6f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + b * a + c^2) + b^2 / (2 * b^2 + c * b + a^2) + c^2 / (2 * c^2 + a * c + b^2)) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 3*a^4*b*c - 4*a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 - 4*a^2*b^4 + 4*a^2*b^3*c - 18*a^2*b^2*c^2 - 4*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 + 3*a*b*c^4 + 2*b^4*c^2 + 3*b^3*c^3 - 4*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (66 : ℝ) * a^3 * (b - a)^3 + (89 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (83 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (30 : ℝ) * a^3 * (c - b)^3 + (65 : ℝ) * a^2 * (b - a)^4 + (110 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (102 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (57 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (11 : ℝ) * a^2 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^5 + (54 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (54 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (37 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (3 : ℝ) * (b - a)^6 + (7 : ℝ) * (b - a)^5 * (c - b)^1 + (7 : ℝ) * (b - a)^4 * (c - b)^2 + (7 : ℝ) * (b - a)^3 * (c - b)^3 + (6 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 3*a^4*b*c - 4*a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 - 4*a^2*b^4 + 4*a^2*b^3*c - 18*a^2*b^2*c^2 - 4*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 + 3*a*b*c^4 + 2*b^4*c^2 + 3*b^3*c^3 - 4*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (c - a)^2 + (24 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^4 * (b - c)^2 + (66 : ℝ) * a^3 * (c - a)^3 + (109 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (103 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (30 : ℝ) * a^3 * (b - c)^3 + (65 : ℝ) * a^2 * (c - a)^4 + (150 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (162 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (77 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (11 : ℝ) * a^2 * (b - c)^4 + (26 : ℝ) * a^1 * (c - a)^5 + (76 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (98 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (61 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (17 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (3 : ℝ) * (c - a)^6 + (11 : ℝ) * (c - a)^5 * (b - c)^1 + (17 : ℝ) * (c - a)^4 * (b - c)^2 + (11 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 3*a^4*b*c - 4*a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 - 4*a^2*b^4 + 4*a^2*b^3*c - 18*a^2*b^2*c^2 - 4*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 + 3*a*b*c^4 + 2*b^4*c^2 + 3*b^3*c^3 - 4*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 3*a^4*b*c - 4*a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 - 4*a^2*b^4 + 4*a^2*b^3*c - 18*a^2*b^2*c^2 - 4*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 + 3*a*b*c^4 + 2*b^4*c^2 + 3*b^3*c^3 - 4*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * a^2 + b * a + c^2) + b^2 / (2 * b^2 + c * b + a^2) + c^2 / (2 * c^2 + a * c + b^2)) ≤ 3 / 4) := @solution
#print axioms solution
