-- Prove2me | solution 1 for WorkbookSource.base_29335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:18.243466+00:00
-- url     : https://prove2.me/submissions/6607fc0d-8878-48b4-a76f-d8e882ec0398

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≥ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b^2 + 10*a^4*b*c + 4*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 + 4*a^3*c^3 - 5*a^2*b^3*c - 18*a^2*b^2*c^2 - 5*a^2*b*c^3 + 2*a^2*c^4 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 + 2*b^4*c^2 + 4*b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^4 * (b - a)^2 + (40 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^4 * (c - b)^2 + (114 : ℝ) * a^3 * (b - a)^3 + (163 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (141 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (46 : ℝ) * a^3 * (c - b)^3 + (114 : ℝ) * a^2 * (b - a)^4 + (212 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (183 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (85 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^2 * (c - b)^4 + (46 : ℝ) * a^1 * (b - a)^5 + (105 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (96 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (47 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (b - a)^6 + (16 : ℝ) * (b - a)^5 * (c - b)^1 + (14 : ℝ) * (b - a)^4 * (c - b)^2 + (4 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b^2 + 10*a^4*b*c + 4*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 + 4*a^3*c^3 - 5*a^2*b^3*c - 18*a^2*b^2*c^2 - 5*a^2*b*c^3 + 2*a^2*c^4 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 + 2*b^4*c^2 + 4*b^3*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^4 * (c - a)^2 + (40 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (40 : ℝ) * a^4 * (b - c)^2 + (114 : ℝ) * a^3 * (c - a)^3 + (179 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (157 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (46 : ℝ) * a^3 * (b - c)^3 + (114 : ℝ) * a^2 * (c - a)^4 + (244 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (231 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (101 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^2 * (b - c)^4 + (46 : ℝ) * a^1 * (c - a)^5 + (125 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (136 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (71 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (14 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * (c - a)^6 + (20 : ℝ) * (c - a)^5 * (b - c)^1 + (24 : ℝ) * (c - a)^4 * (b - c)^2 + (12 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^2 + 10*a^4*b*c + 4*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 + 4*a^3*c^3 - 5*a^2*b^3*c - 18*a^2*b^2*c^2 - 5*a^2*b*c^3 + 2*a^2*c^4 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 + 2*b^4*c^2 + 4*b^3*c^3) := by
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
  have hn : 0 ≤ (2*a^4*b^2 + 10*a^4*b*c + 4*a^3*b^3 - 5*a^3*b^2*c - 5*a^3*b*c^2 + 4*a^3*c^3 - 5*a^2*b^3*c - 18*a^2*b^2*c^2 - 5*a^2*b*c^3 + 2*a^2*c^4 + 10*a*b^4*c - 5*a*b^3*c^2 - 5*a*b^2*c^3 + 10*a*b*c^4 + 2*b^4*c^2 + 4*b^3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≥ 3 / 4) := @solution
#print axioms solution
