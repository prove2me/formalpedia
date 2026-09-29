-- Prove2me | solution 1 for WorkbookSource.base_2714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:14.277432+00:00
-- url     : https://prove2.me/submissions/f1bc6f5a-5d33-4f4e-87e5-9832f30a473d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a * b * (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + a * c + b * c) + b * c * (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + b * a + c * a) + c * a * (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + c * b + a * b)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b + a^7*c - 2*a^6*b*c - a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 - a^5*c^3 - a^4*b^3*c - 4*a^4*b^2*c^2 - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c + 4*a^3*b^3*c^2 + 4*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 + 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^7 - 2*a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 2*a*b^2*c^5 - 2*a*b*c^6 + a*c^7 + b^7*c - b^5*c^3 - b^3*c^5 + b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (b - a)^2 + (8 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^6 * (c - b)^2 + (18 : ℝ) * a^5 * (b - a)^3 + (27 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (69 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (30 : ℝ) * a^5 * (c - b)^3 + (14 : ℝ) * a^4 * (b - a)^4 + (28 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (177 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (163 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (44 : ℝ) * a^4 * (c - b)^4 + (4 : ℝ) * a^3 * (b - a)^5 + (10 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (216 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (314 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (168 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (32 : ℝ) * a^3 * (c - b)^5 + (144 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (288 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (228 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (84 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^2 * (c - b)^6 + (52 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (130 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (134 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (71 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (19 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * a^1 * (c - b)^7 + (8 : ℝ) * (b - a)^6 * (c - b)^2 + (24 : ℝ) * (b - a)^5 * (c - b)^3 + (30 : ℝ) * (b - a)^4 * (c - b)^4 + (20 : ℝ) * (b - a)^3 * (c - b)^5 + (7 : ℝ) * (b - a)^2 * (c - b)^6 + (1 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b + a^7*c - 2*a^6*b*c - a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 - a^5*c^3 - a^4*b^3*c - 4*a^4*b^2*c^2 - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c + 4*a^3*b^3*c^2 + 4*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 + 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^7 - 2*a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 2*a*b^2*c^5 - 2*a*b*c^6 + a*c^7 + b^7*c - b^5*c^3 - b^3*c^5 + b*c^7) := by
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
  have hn : 0 ≤ (a^7*b + a^7*c - 2*a^6*b*c - a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 - a^5*c^3 - a^4*b^3*c - 4*a^4*b^2*c^2 - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c + 4*a^3*b^3*c^2 + 4*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 + 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^7 - 2*a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 2*a*b^2*c^5 - 2*a*b*c^6 + a*c^7 + b^7*c - b^5*c^3 - b^3*c^5 + b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + a * c + b * c) + b * c * (b ^ 2 + c ^ 2) / (b ^ 2 + c ^ 2 + b * a + c * a) + c * a * (c ^ 2 + a ^ 2) / (c ^ 2 + a ^ 2 + c * b + a * b)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2) := @solution
#print axioms solution
