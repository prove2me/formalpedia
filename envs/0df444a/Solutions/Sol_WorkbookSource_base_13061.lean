-- Prove2me | solution 1 for WorkbookSource.base_13061
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:50:55.508651+00:00
-- url     : https://prove2.me/submissions/853bfea7-f065-4cd6-99a7-d3393c0a83de

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 3 * b * c) / (b + c) + (b^2 + 3 * c * a) / (c + a) + (c^2 + 3 * a * b) / (a + b) ≥ (21 + 3 * a * b * c) / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6/9 + 5*a^5*b/9 + 5*a^5*c/9 - 4*a^4*b^2/9 + 8*a^4*b*c/9 - 4*a^4*c^2/9 - 10*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 10*a^3*c^3/9 - 4*a^2*b^4/9 - 4*a^2*b^3*c/9 + 4*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 - 4*a^2*c^4/9 + 5*a*b^5/9 + 8*a*b^4*c/9 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 8*a*b*c^4/9 + 5*a*c^5/9 + 4*b^6/9 + 5*b^5*c/9 - 4*b^4*c^2/9 - 10*b^3*c^3/9 - 4*b^2*c^4/9 + 5*b*c^5/9 + 4*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (136/9 : ℝ) * a^3 * (b - a)^3 + (68/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (124/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (152/9 : ℝ) * a^3 * (c - b)^3 + (86/9 : ℝ) * a^2 * (b - a)^4 + (172/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (178/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (448/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (110/9 : ℝ) * a^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^5 + (5 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (290/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (130/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (65/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (34/9 : ℝ) * a^1 * (c - b)^5 + (52/9 : ℝ) * (b - a)^4 * (c - b)^2 + (104/9 : ℝ) * (b - a)^3 * (c - b)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^4 + (29/9 : ℝ) * (b - a)^1 * (c - b)^5 + (4/9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6/9 + 5*a^5*b/9 + 5*a^5*c/9 - 4*a^4*b^2/9 + 8*a^4*b*c/9 - 4*a^4*c^2/9 - 10*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 10*a^3*c^3/9 - 4*a^2*b^4/9 - 4*a^2*b^3*c/9 + 4*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 - 4*a^2*c^4/9 + 5*a*b^5/9 + 8*a*b^4*c/9 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 8*a*b*c^4/9 + 5*a*c^5/9 + 4*b^6/9 + 5*b^5*c/9 - 4*b^4*c^2/9 - 10*b^3*c^3/9 - 4*b^2*c^4/9 + 5*b*c^5/9 + 4*c^6/9) := by
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
  have he : (4*a^4 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*b + 4*a^3*c - 3*a^2*b^3*c - 6*a^2*b^2*c^2 + 12*a^2*b^2 - 3*a^2*b*c^3 + 40*a^2*b*c - 21*a^2*b + 12*a^2*c^2 - 21*a^2*c - 3*a*b^3*c^2 + 4*a*b^3 - 3*a*b^2*c^3 + 40*a*b^2*c - 21*a*b^2 + 40*a*b*c^2 - 42*a*b*c + 4*a*c^3 - 21*a*c^2 + 4*b^4 + 4*b^3*c + 12*b^2*c^2 - 21*b^2*c + 4*b*c^3 - 21*b*c^2 + 4*c^4) = (4*a^6/9 + 5*a^5*b/9 + 5*a^5*c/9 - 4*a^4*b^2/9 + 8*a^4*b*c/9 - 4*a^4*c^2/9 - 10*a^3*b^3/9 - 4*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 10*a^3*c^3/9 - 4*a^2*b^4/9 - 4*a^2*b^3*c/9 + 4*a^2*b^2*c^2/3 - 4*a^2*b*c^3/9 - 4*a^2*c^4/9 + 5*a*b^5/9 + 8*a*b^4*c/9 - 4*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + 8*a*b*c^4/9 + 5*a*c^5/9 + 4*b^6/9 + 5*b^5*c/9 - 4*b^4*c^2/9 - 10*b^3*c^3/9 - 4*b^2*c^4/9 + 5*b*c^5/9 + 4*c^6/9) := by
    linear_combination (-4*a^5/9 - a^4*b/9 - a^4*c/9 - 4*a^4/3 + 5*a^3*b^2/9 - 2*a^3*b*c/3 + a^3*b + 5*a^3*c^2/9 + a^3*c + 5*a^2*b^3/9 - 22*a^2*b^2*c/9 + 2*a^2*b^2/3 - 22*a^2*b*c^2/9 - 4*a^2*b*c + 7*a^2*b + 5*a^2*c^3/9 + 2*a^2*c^2/3 + 7*a^2*c - a*b^4/9 - 2*a*b^3*c/3 + a*b^3 - 22*a*b^2*c^2/9 - 4*a*b^2*c + 7*a*b^2 - 2*a*b*c^3/3 - 4*a*b*c^2 + 14*a*b*c - a*c^4/9 + a*c^3 + 7*a*c^2 - 4*b^5/9 - b^4*c/9 - 4*b^4/3 + 5*b^3*c^2/9 + b^3*c + 5*b^2*c^3/9 + 2*b^2*c^2/3 + 7*b^2*c - b*c^4/9 + b*c^3 + 7*b*c^2 - 4*c^5/9 - 4*c^4/3) * habc
  have hn : 0 ≤ (4*a^4 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 4*a^3*b + 4*a^3*c - 3*a^2*b^3*c - 6*a^2*b^2*c^2 + 12*a^2*b^2 - 3*a^2*b*c^3 + 40*a^2*b*c - 21*a^2*b + 12*a^2*c^2 - 21*a^2*c - 3*a*b^3*c^2 + 4*a*b^3 - 3*a*b^2*c^3 + 40*a*b^2*c - 21*a*b^2 + 40*a*b*c^2 - 42*a*b*c + 4*a*c^3 - 21*a*c^2 + 4*b^4 + 4*b^3*c + 12*b^2*c^2 - 21*b^2*c + 4*b*c^3 - 21*b*c^2 + 4*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + 3 * b * c) / (b + c) + (b^2 + 3 * c * a) / (c + a) + (c^2 + 3 * a * b) / (a + b) ≥ (21 + 3 * a * b * c) / 4) := @solution
#print axioms solution
