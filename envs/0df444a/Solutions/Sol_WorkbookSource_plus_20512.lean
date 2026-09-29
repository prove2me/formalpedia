-- Prove2me | solution 1 for WorkbookSource.plus_20512
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:55.563158+00:00
-- url     : https://prove2.me/submissions/644fa1c9-a19c-4969-87b9-327bfb21a7e2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≤ (a^2 + b^2 + c^2)^2 / (6 * a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 4*a^5*b*c + a^5*c^2 + 2*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 + 4*a^3*b^3*c - 2*a^3*b^2*c^2 + 4*a^3*b*c^3 + 2*a^3*c^4 + a^2*b^5 - 3*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 3*a^2*b*c^4 + a^2*c^5 + a*b^6 - 4*a*b^5*c - 3*a*b^4*c^2 + 4*a*b^3*c^3 - 3*a*b^2*c^4 - 4*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 + 2*b^4*c^3 + 2*b^3*c^4 + b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^5 * (b - a)^2 + (20 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^5 * (c - b)^2 + (78 : ℝ) * a^4 * (b - a)^3 + (117 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (83 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (22 : ℝ) * a^4 * (c - b)^3 + (130 : ℝ) * a^3 * (b - a)^4 + (260 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (210 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (80 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^3 * (c - b)^4 + (112 : ℝ) * a^2 * (b - a)^5 + (280 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (288 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (152 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (52 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^2 * (c - b)^5 + (48 : ℝ) * a^1 * (b - a)^6 + (144 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (186 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (132 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (58 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^7 + (28 : ℝ) * (b - a)^6 * (c - b)^1 + (44 : ℝ) * (b - a)^5 * (c - b)^2 + (40 : ℝ) * (b - a)^4 * (c - b)^3 + (22 : ℝ) * (b - a)^3 * (c - b)^4 + (7 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 4*a^5*b*c + a^5*c^2 + 2*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 + 4*a^3*b^3*c - 2*a^3*b^2*c^2 + 4*a^3*b*c^3 + 2*a^3*c^4 + a^2*b^5 - 3*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 3*a^2*b*c^4 + a^2*c^5 + a*b^6 - 4*a*b^5*c - 3*a*b^4*c^2 + 4*a*b^3*c^3 - 3*a*b^2*c^4 - 4*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 + 2*b^4*c^3 + 2*b^3*c^4 + b^2*c^5 + b*c^6) := by
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
  have hn : 0 ≤ (a^6*b + a^6*c + a^5*b^2 - 4*a^5*b*c + a^5*c^2 + 2*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 + 4*a^3*b^3*c - 2*a^3*b^2*c^2 + 4*a^3*b*c^3 + 2*a^3*c^4 + a^2*b^5 - 3*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 3*a^2*b*c^4 + a^2*c^5 + a*b^6 - 4*a*b^5*c - 3*a*b^4*c^2 + 4*a*b^3*c^3 - 3*a*b^2*c^4 - 4*a*b*c^5 + a*c^6 + b^6*c + b^5*c^2 + 2*b^4*c^3 + 2*b^3*c^4 + b^2*c^5 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≤ (a^2 + b^2 + c^2)^2 / (6 * a * b * c)) := @solution
#print axioms solution
