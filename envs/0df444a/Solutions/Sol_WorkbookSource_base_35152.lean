-- Prove2me | solution 1 for WorkbookSource.base_35152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:22.114625+00:00
-- url     : https://prove2.me/submissions/c67ef84f-8332-469c-8cd0-679374b24945

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 1 / (2 * c ^ 2 + a ^ 2 + b ^ 2)) ≤ (3 / 4)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (34*a^6/9 - 40*a^5*b/9 - 40*a^5*c/9 + 125*a^4*b^2/9 - 40*a^4*b*c/9 + 125*a^4*c^2/9 - 88*a^3*b^3/9 - 88*a^3*b^2*c/9 - 88*a^3*b*c^2/9 - 88*a^3*c^3/9 + 125*a^2*b^4/9 - 88*a^2*b^3*c/9 + 100*a^2*b^2*c^2/3 - 88*a^2*b*c^3/9 + 125*a^2*c^4/9 - 40*a*b^5/9 - 40*a*b^4*c/9 - 88*a*b^3*c^2/9 - 88*a*b^2*c^3/9 - 40*a*b*c^4/9 - 40*a*c^5/9 + 34*b^6/9 - 40*b^5*c/9 + 125*b^4*c^2/9 - 88*b^3*c^3/9 + 125*b^2*c^4/9 - 40*b*c^5/9 + 34*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^4 * (b - a)^2 + (32 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^4 * (c - b)^2 + (784/9 : ℝ) * a^3 * (b - a)^3 + (392/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (376/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (368/9 : ℝ) * a^3 * (c - b)^3 + (944/9 : ℝ) * a^2 * (b - a)^4 + (1888/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (712/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1192/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (320/9 : ℝ) * a^2 * (c - b)^4 + (188/3 : ℝ) * a^1 * (b - a)^5 + (470/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1892/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (476/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (70 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (124/9 : ℝ) * a^1 * (c - b)^5 + (50/3 : ℝ) * (b - a)^6 + (50 : ℝ) * (b - a)^5 * (c - b)^1 + (721/9 : ℝ) * (b - a)^4 * (c - b)^2 + (692/9 : ℝ) * (b - a)^3 * (c - b)^3 + (145/3 : ℝ) * (b - a)^2 * (c - b)^4 + (164/9 : ℝ) * (b - a)^1 * (c - b)^5 + (34/9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (34*a^6/9 - 40*a^5*b/9 - 40*a^5*c/9 + 125*a^4*b^2/9 - 40*a^4*b*c/9 + 125*a^4*c^2/9 - 88*a^3*b^3/9 - 88*a^3*b^2*c/9 - 88*a^3*b*c^2/9 - 88*a^3*c^3/9 + 125*a^2*b^4/9 - 88*a^2*b^3*c/9 + 100*a^2*b^2*c^2/3 - 88*a^2*b*c^3/9 + 125*a^2*c^4/9 - 40*a*b^5/9 - 40*a*b^4*c/9 - 88*a*b^3*c^2/9 - 88*a*b^2*c^3/9 - 40*a*b*c^4/9 - 40*a*c^5/9 + 34*b^6/9 - 40*b^5*c/9 + 125*b^4*c^2/9 - 88*b^3*c^3/9 + 125*b^2*c^4/9 - 40*b*c^5/9 + 34*c^6/9) := by
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
  have he : (6*a^6 + 21*a^4*b^2 + 21*a^4*c^2 - 20*a^4 + 21*a^2*b^4 + 48*a^2*b^2*c^2 - 44*a^2*b^2 + 21*a^2*c^4 - 44*a^2*c^2 + 6*b^6 + 21*b^4*c^2 - 20*b^4 + 21*b^2*c^4 - 44*b^2*c^2 + 6*c^6 - 20*c^4) = (34*a^6/9 - 40*a^5*b/9 - 40*a^5*c/9 + 125*a^4*b^2/9 - 40*a^4*b*c/9 + 125*a^4*c^2/9 - 88*a^3*b^3/9 - 88*a^3*b^2*c/9 - 88*a^3*b*c^2/9 - 88*a^3*c^3/9 + 125*a^2*b^4/9 - 88*a^2*b^3*c/9 + 100*a^2*b^2*c^2/3 - 88*a^2*b*c^3/9 + 125*a^2*c^4/9 - 40*a*b^5/9 - 40*a*b^4*c/9 - 88*a*b^3*c^2/9 - 88*a*b^2*c^3/9 - 40*a*b*c^4/9 - 40*a*c^5/9 + 34*b^6/9 - 40*b^5*c/9 + 125*b^4*c^2/9 - 88*b^3*c^3/9 + 125*b^2*c^4/9 - 40*b*c^5/9 + 34*c^6/9) := by
    linear_combination (20*a^5/9 + 20*a^4*b/9 + 20*a^4*c/9 + 20*a^4/3 + 44*a^3*b^2/9 + 44*a^3*c^2/9 + 44*a^2*b^3/9 + 44*a^2*b^2*c/9 + 44*a^2*b^2/3 + 44*a^2*b*c^2/9 + 44*a^2*c^3/9 + 44*a^2*c^2/3 + 20*a*b^4/9 + 44*a*b^2*c^2/9 + 20*a*c^4/9 + 20*b^5/9 + 20*b^4*c/9 + 20*b^4/3 + 44*b^3*c^2/9 + 44*b^2*c^3/9 + 44*b^2*c^2/3 + 20*b*c^4/9 + 20*c^5/9 + 20*c^4/3) * hab
  have hn : 0 ≤ (6*a^6 + 21*a^4*b^2 + 21*a^4*c^2 - 20*a^4 + 21*a^2*b^4 + 48*a^2*b^2*c^2 - 44*a^2*b^2 + 21*a^2*c^4 - 44*a^2*c^2 + 6*b^6 + 21*b^4*c^2 - 20*b^4 + 21*b^2*c^4 - 44*b^2*c^2 + 6*c^6 - 20*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (1 / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 1 / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 1 / (2 * c ^ 2 + a ^ 2 + b ^ 2)) ≤ (3 / 4)) := @solution
#print axioms solution
