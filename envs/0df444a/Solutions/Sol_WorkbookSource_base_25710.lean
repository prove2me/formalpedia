-- Prove2me | solution 1 for WorkbookSource.base_25710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:28.980815+00:00
-- url     : https://prove2.me/submissions/806edbef-1da8-4a28-851c-6422f3545cfd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≤ (a + b + c) / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (15*a^5*b^2 + 9*a^5*c^2 + 15*a^4*b^3 - 25*a^4*b^2*c - 15*a^4*b*c^2 - 15*a^4*c^3 - 15*a^3*b^4 + 16*a^3*b^2*c^2 + 15*a^3*c^4 + 9*a^2*b^5 - 15*a^2*b^4*c + 16*a^2*b^3*c^2 + 16*a^2*b^2*c^3 - 25*a^2*b*c^4 + 15*a^2*c^5 - 25*a*b^4*c^2 - 15*a*b^2*c^4 + 15*b^5*c^2 + 15*b^4*c^3 - 15*b^3*c^4 + 9*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^5 * (b - a)^2 + (64 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (64 : ℝ) * a^5 * (c - b)^2 + (224 : ℝ) * a^4 * (b - a)^3 + (216 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (184 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (96 : ℝ) * a^4 * (c - b)^3 + (336 : ℝ) * a^3 * (b - a)^4 + (352 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (208 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (192 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (80 : ℝ) * a^3 * (c - b)^4 + (280 : ℝ) * a^2 * (b - a)^5 + (390 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (204 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (156 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (110 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^2 * (c - b)^5 + (128 : ℝ) * a^1 * (b - a)^6 + (250 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (185 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (120 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (75 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (24 : ℝ) * (b - a)^7 + (60 : ℝ) * (b - a)^6 * (c - b)^1 + (60 : ℝ) * (b - a)^5 * (c - b)^2 + (45 : ℝ) * (b - a)^4 * (c - b)^3 + (30 : ℝ) * (b - a)^3 * (c - b)^4 + (9 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (15*a^5*b^2 + 9*a^5*c^2 + 15*a^4*b^3 - 25*a^4*b^2*c - 15*a^4*b*c^2 - 15*a^4*c^3 - 15*a^3*b^4 + 16*a^3*b^2*c^2 + 15*a^3*c^4 + 9*a^2*b^5 - 15*a^2*b^4*c + 16*a^2*b^3*c^2 + 16*a^2*b^2*c^3 - 25*a^2*b*c^4 + 15*a^2*c^5 - 25*a*b^4*c^2 - 15*a*b^2*c^4 + 15*b^5*c^2 + 15*b^4*c^3 - 15*b^3*c^4 + 9*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^5 * (c - a)^2 + (64 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (64 : ℝ) * a^5 * (b - c)^2 + (224 : ℝ) * a^4 * (c - a)^3 + (456 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (424 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (96 : ℝ) * a^4 * (b - c)^3 + (336 : ℝ) * a^3 * (c - a)^4 + (992 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (1168 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (512 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (80 : ℝ) * a^3 * (b - c)^4 + (280 : ℝ) * a^2 * (c - a)^5 + (1010 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (1444 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (916 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (250 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (24 : ℝ) * a^2 * (b - c)^5 + (128 : ℝ) * a^1 * (c - a)^6 + (518 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (855 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (680 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (245 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (30 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (24 : ℝ) * (c - a)^7 + (108 : ℝ) * (c - a)^6 * (b - c)^1 + (204 : ℝ) * (c - a)^5 * (b - c)^2 + (195 : ℝ) * (c - a)^4 * (b - c)^3 + (90 : ℝ) * (c - a)^3 * (b - c)^4 + (15 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (15*a^5*b^2 + 9*a^5*c^2 + 15*a^4*b^3 - 25*a^4*b^2*c - 15*a^4*b*c^2 - 15*a^4*c^3 - 15*a^3*b^4 + 16*a^3*b^2*c^2 + 15*a^3*c^4 + 9*a^2*b^5 - 15*a^2*b^4*c + 16*a^2*b^3*c^2 + 16*a^2*b^2*c^3 - 25*a^2*b*c^4 + 15*a^2*c^5 - 25*a*b^4*c^2 - 15*a*b^2*c^4 + 15*b^5*c^2 + 15*b^4*c^3 - 15*b^3*c^4 + 9*b^2*c^5) := by
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
  have hn : 0 ≤ (15*a^5*b^2 + 9*a^5*c^2 + 15*a^4*b^3 - 25*a^4*b^2*c - 15*a^4*b*c^2 - 15*a^4*c^3 - 15*a^3*b^4 + 16*a^3*b^2*c^2 + 15*a^3*c^4 + 9*a^2*b^5 - 15*a^2*b^4*c + 16*a^2*b^3*c^2 + 16*a^2*b^2*c^3 - 25*a^2*b*c^4 + 15*a^2*c^5 - 25*a*b^4*c^2 - 15*a*b^2*c^4 + 15*b^5*c^2 + 15*b^4*c^3 - 15*b^3*c^4 + 9*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≤ (a + b + c) / 4) := @solution
#print axioms solution
