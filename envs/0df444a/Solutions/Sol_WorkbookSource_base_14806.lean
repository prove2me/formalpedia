-- Prove2me | solution 1 for WorkbookSource.base_14806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:16.714086+00:00
-- url     : https://prove2.me/submissions/3d43f397-c394-4cce-872f-554b5633b8b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ (2 * a / (3 * a ^ 2 + b * c) + 2 * b / (3 * b ^ 2 + c * a) + 2 * c / (3 * c ^ 2 + a * b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b*c + 3*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 3*a^5*c^3 + 15*a^4*b^4 - 8*a^4*b^3*c - 15*a^4*b^2*c^2 - 8*a^4*b*c^3 + 15*a^4*c^4 + 3*a^3*b^5 - 8*a^3*b^4*c + 5*a^3*b^3*c^2 + 5*a^3*b^2*c^3 - 8*a^3*b*c^4 + 3*a^3*c^5 + a^2*b^5*c - 15*a^2*b^4*c^2 + 5*a^2*b^3*c^3 - 15*a^2*b^2*c^4 + a^2*b*c^5 + 3*a*b^6*c + a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 + a*b^2*c^5 + 3*a*b*c^6 + 3*b^5*c^3 + 15*b^4*c^4 + 3*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (b - a)^2 + (96 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^6 * (c - b)^2 + (440 : ℝ) * a^5 * (b - a)^3 + (660 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (492 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (136 : ℝ) * a^5 * (c - b)^3 + (844 : ℝ) * a^4 * (b - a)^4 + (1688 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1352 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (508 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (84 : ℝ) * a^4 * (c - b)^4 + (870 : ℝ) * a^3 * (b - a)^5 + (2175 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2102 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (978 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (233 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (26 : ℝ) * a^3 * (c - b)^5 + (509 : ℝ) * a^2 * (b - a)^6 + (1527 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1775 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1005 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (296 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (48 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^2 * (c - b)^6 + (160 : ℝ) * a^1 * (b - a)^7 + (560 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (758 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (495 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (162 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (28 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (21 : ℝ) * (b - a)^8 + (84 : ℝ) * (b - a)^7 * (c - b)^1 + (129 : ℝ) * (b - a)^6 * (c - b)^2 + (93 : ℝ) * (b - a)^5 * (c - b)^3 + (30 : ℝ) * (b - a)^4 * (c - b)^4 + (3 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b*c + 3*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 3*a^5*c^3 + 15*a^4*b^4 - 8*a^4*b^3*c - 15*a^4*b^2*c^2 - 8*a^4*b*c^3 + 15*a^4*c^4 + 3*a^3*b^5 - 8*a^3*b^4*c + 5*a^3*b^3*c^2 + 5*a^3*b^2*c^3 - 8*a^3*b*c^4 + 3*a^3*c^5 + a^2*b^5*c - 15*a^2*b^4*c^2 + 5*a^2*b^3*c^3 - 15*a^2*b^2*c^4 + a^2*b*c^5 + 3*a*b^6*c + a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 + a*b^2*c^5 + 3*a*b*c^6 + 3*b^5*c^3 + 15*b^4*c^4 + 3*b^3*c^5) := by
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
  have hn : 0 ≤ (3*a^6*b*c + 3*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 3*a^5*c^3 + 15*a^4*b^4 - 8*a^4*b^3*c - 15*a^4*b^2*c^2 - 8*a^4*b*c^3 + 15*a^4*c^4 + 3*a^3*b^5 - 8*a^3*b^4*c + 5*a^3*b^3*c^2 + 5*a^3*b^2*c^3 - 8*a^3*b*c^4 + 3*a^3*c^5 + a^2*b^5*c - 15*a^2*b^4*c^2 + 5*a^2*b^3*c^3 - 15*a^2*b^2*c^4 + a^2*b*c^5 + 3*a*b^6*c + a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 + a*b^2*c^5 + 3*a*b*c^6 + 3*b^5*c^3 + 15*b^4*c^4 + 3*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≥ (2 * a / (3 * a ^ 2 + b * c) + 2 * b / (3 * b ^ 2 + c * a) + 2 * c / (3 * c ^ 2 + a * b))) := @solution
#print axioms solution
