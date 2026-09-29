-- Prove2me | solution 1 for WorkbookSource.base_53800
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:34.05605+00:00
-- url     : https://prove2.me/submissions/4e71484d-eeb8-426e-b8e3-866dbf16f991

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^3 + 2 * a * b * c + c^3) / (a^2 + b * c) + (c^3 + 2 * b * c * a + a^3) / (b^2 + c * a) + (a^3 + 2 * c * a * b + b^3) / (c^2 + a * b) ≥ 2 * (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 2*a^5*b*c + a^5*c^2 - 2*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 - 2*a^3*c^4 + a^2*b^5 + a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a^2*b*c^4 + a^2*c^5 + a*b^6 - 2*a*b^5*c + a*b^4*c^2 + 2*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^5 * (b - a)^2 + (12 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^5 * (c - b)^2 + (30 : ℝ) * a^4 * (b - a)^3 + (45 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (75 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (30 : ℝ) * a^4 * (c - b)^3 + (28 : ℝ) * a^3 * (b - a)^4 + (56 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (144 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (116 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (28 : ℝ) * a^3 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^5 + (30 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (120 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (150 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (72 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^6 + (6 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (48 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (86 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (60 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^5 * (c - b)^2 + (20 : ℝ) * (b - a)^4 * (c - b)^3 + (18 : ℝ) * (b - a)^3 * (c - b)^4 + (7 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 2*a^5*b*c + a^5*c^2 - 2*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 - 2*a^3*c^4 + a^2*b^5 + a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a^2*b*c^4 + a^2*c^5 + a*b^6 - 2*a*b^5*c + a*b^4*c^2 + 2*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5 + b*c^6) := by
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
  have hn : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 2*a^5*b*c + a^5*c^2 - 2*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 2*a^3*b^3*c - 2*a^3*b^2*c^2 + 2*a^3*b*c^3 - 2*a^3*c^4 + a^2*b^5 + a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a^2*b*c^4 + a^2*c^5 + a*b^6 - 2*a*b^5*c + a*b^4*c^2 + 2*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b^3 + 2 * a * b * c + c^3) / (a^2 + b * c) + (c^3 + 2 * b * c * a + a^3) / (b^2 + c * a) + (a^3 + 2 * c * a * b + b^3) / (c^2 + a * b) ≥ 2 * (a + b + c)) := @solution
#print axioms solution
