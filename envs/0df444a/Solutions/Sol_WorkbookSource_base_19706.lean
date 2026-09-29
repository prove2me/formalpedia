-- Prove2me | solution 1 for WorkbookSource.base_19706
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:42:15.072052+00:00
-- url     : https://prove2.me/submissions/c33d0bfb-2136-4ecb-88ca-c419a86e40c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / (b^2 + b * c + a) + b^3 / (c^2 + c * a + b) + c^3 / (a^2 + a * b + c) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6*b/27 + 8*a^6*c/9 + 14*a^5*b^2/27 + 80*a^5*b*c/81 + 26*a^5*c^2/27 + a^4*b^3/3 - 49*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 11*a^3*b^3*c/9 - 68*a^3*b^2*c^2/27 - 11*a^3*b*c^3/9 + a^3*c^4/3 + 26*a^2*b^5/27 + 14*a^2*b^4*c/81 - 68*a^2*b^3*c^2/27 - 68*a^2*b^2*c^3/27 - 49*a^2*b*c^4/81 + 14*a^2*c^5/27 + 8*a*b^6/9 + 80*a*b^5*c/81 - 49*a*b^4*c^2/81 - 11*a*b^3*c^3/9 + 14*a*b^2*c^4/81 + 80*a*b*c^5/81 + 8*a*c^6/27 + 8*b^6*c/27 + 14*b^5*c^2/27 + b^4*c^3/3 + 5*b^3*c^4/27 + 26*b^2*c^5/27 + 8*b*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (77/3 : ℝ) * a^5 * (b - a)^2 + (77/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (77/3 : ℝ) * a^5 * (c - b)^2 + (2269/27 : ℝ) * a^4 * (b - a)^3 + (1211/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (1252/9 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (1196/27 : ℝ) * a^4 * (c - b)^3 + (8885/81 : ℝ) * a^3 * (b - a)^4 + (19606/81 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (7903/27 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (12988/81 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (2447/81 : ℝ) * a^3 * (c - b)^4 + (5827/81 : ℝ) * a^2 * (b - a)^5 + (16498/81 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (23632/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (17573/81 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (6164/81 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (776/81 : ℝ) * a^2 * (c - b)^5 + (1928/81 : ℝ) * a^1 * (b - a)^6 + (2237/27 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (11263/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (10465/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (581/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (1244/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (32/27 : ℝ) * a^1 * (c - b)^6 + (86/27 : ℝ) * (b - a)^7 + (119/9 : ℝ) * (b - a)^6 * (c - b)^1 + (691/27 : ℝ) * (b - a)^5 * (c - b)^2 + (769/27 : ℝ) * (b - a)^4 * (c - b)^3 + (55/3 : ℝ) * (b - a)^3 * (c - b)^4 + (170/27 : ℝ) * (b - a)^2 * (c - b)^5 + (8/9 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^6*b/27 + 8*a^6*c/9 + 14*a^5*b^2/27 + 80*a^5*b*c/81 + 26*a^5*c^2/27 + a^4*b^3/3 - 49*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 11*a^3*b^3*c/9 - 68*a^3*b^2*c^2/27 - 11*a^3*b*c^3/9 + a^3*c^4/3 + 26*a^2*b^5/27 + 14*a^2*b^4*c/81 - 68*a^2*b^3*c^2/27 - 68*a^2*b^2*c^3/27 - 49*a^2*b*c^4/81 + 14*a^2*c^5/27 + 8*a*b^6/9 + 80*a*b^5*c/81 - 49*a*b^4*c^2/81 - 11*a*b^3*c^3/9 + 14*a*b^2*c^4/81 + 80*a*b*c^5/81 + 8*a*c^6/27 + 8*b^6*c/27 + 14*b^5*c^2/27 + b^4*c^3/3 + 5*b^3*c^4/27 + 26*b^2*c^5/27 + 8*b*c^6/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (77/3 : ℝ) * a^5 * (c - a)^2 + (77/3 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (77/3 : ℝ) * a^5 * (b - c)^2 + (2269/27 : ℝ) * a^4 * (c - a)^3 + (1058/9 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (1099/9 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (1196/27 : ℝ) * a^4 * (b - c)^3 + (8885/81 : ℝ) * a^3 * (c - a)^4 + (15934/81 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (6067/27 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (11152/81 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (2447/81 : ℝ) * a^3 * (b - c)^4 + (5827/81 : ℝ) * a^2 * (c - a)^5 + (12637/81 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (15910/81 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (12605/81 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (5057/81 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (776/81 : ℝ) * a^2 * (b - c)^5 + (1928/81 : ℝ) * a^1 * (c - a)^6 + (1619/27 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (6628/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (6037/81 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (358/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (884/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (32/27 : ℝ) * a^1 * (b - c)^6 + (86/27 : ℝ) * (c - a)^7 + (245/27 : ℝ) * (c - a)^6 * (b - c)^1 + (355/27 : ℝ) * (c - a)^5 * (b - c)^2 + (341/27 : ℝ) * (c - a)^4 * (b - c)^3 + (199/27 : ℝ) * (c - a)^3 * (b - c)^4 + (62/27 : ℝ) * (c - a)^2 * (b - c)^5 + (8/27 : ℝ) * (c - a)^1 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6*b/27 + 8*a^6*c/9 + 14*a^5*b^2/27 + 80*a^5*b*c/81 + 26*a^5*c^2/27 + a^4*b^3/3 - 49*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 11*a^3*b^3*c/9 - 68*a^3*b^2*c^2/27 - 11*a^3*b*c^3/9 + a^3*c^4/3 + 26*a^2*b^5/27 + 14*a^2*b^4*c/81 - 68*a^2*b^3*c^2/27 - 68*a^2*b^2*c^3/27 - 49*a^2*b*c^4/81 + 14*a^2*c^5/27 + 8*a*b^6/9 + 80*a*b^5*c/81 - 49*a*b^4*c^2/81 - 11*a*b^3*c^3/9 + 14*a*b^2*c^4/81 + 80*a*b*c^5/81 + 8*a*c^6/27 + 8*b^6*c/27 + 14*b^5*c^2/27 + b^4*c^3/3 + 5*b^3*c^4/27 + 26*b^2*c^5/27 + 8*b*c^6/9) := by
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
  have he : (a^6*c + a^5*b*c + a^5*b + a^5*c^2 + a^4*b^2 + a^4*b*c^2 + a^4*c^2 - a^4*c + a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - a^3*b + a^3*c^3 - a^3*c^2 + a^2*b^5 + a^2*b^4*c + a^2*b^4 - a^2*b^3*c - a^2*b^3 - 2*a^2*b^2*c^2 - a^2*b^2*c - a^2*b^2 - a^2*b*c^3 - a^2*b*c^2 + a^2*c^4 - a^2*c^2 + a*b^6 + a*b^5*c - a*b^4 - a*b^3*c^2 + a*b^2*c^4 - a*b^2*c^3 - a*b^2*c^2 + a*b*c^5 - a*b*c + a*c^5 - a*c^3 + b^5*c + b^4*c^2 + b^3*c^3 - b^3*c + b^2*c^5 + b^2*c^4 - b^2*c^3 - b^2*c^2 + b*c^6 - b*c^4) = (8*a^6*b/27 + 8*a^6*c/9 + 14*a^5*b^2/27 + 80*a^5*b*c/81 + 26*a^5*c^2/27 + a^4*b^3/3 - 49*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 11*a^3*b^3*c/9 - 68*a^3*b^2*c^2/27 - 11*a^3*b*c^3/9 + a^3*c^4/3 + 26*a^2*b^5/27 + 14*a^2*b^4*c/81 - 68*a^2*b^3*c^2/27 - 68*a^2*b^2*c^3/27 - 49*a^2*b*c^4/81 + 14*a^2*c^5/27 + 8*a*b^6/9 + 80*a*b^5*c/81 - 49*a*b^4*c^2/81 - 11*a*b^3*c^3/9 + 14*a*b^2*c^4/81 + 80*a*b*c^5/81 + 8*a*c^6/27 + 8*b^6*c/27 + 14*b^5*c^2/27 + b^4*c^3/3 + 5*b^3*c^4/27 + 26*b^2*c^5/27 + 8*b*c^6/9) := by
    linear_combination (-8*a^5*b/27 + a^5*c/9 - 2*a^4*b^2/9 + 16*a^4*b*c/81 + a^4*b/9 - 2*a^4*c^2/27 + a^4*c/3 - a^3*b^3/9 + 17*a^3*b^2*c/27 + 2*a^3*b^2/9 + 19*a^3*b*c^2/27 + 4*a^3*b*c/27 + a^3*b/3 - a^3*c^3/9 + 4*a^3*c^2/9 - 2*a^2*b^4/27 + 19*a^2*b^3*c/27 + 4*a^2*b^3/9 + 32*a^2*b^2*c^2/27 + 14*a^2*b^2*c/27 + a^2*b^2/3 + 17*a^2*b*c^3/27 + 14*a^2*b*c^2/27 + a^2*b*c/9 - 2*a^2*c^4/9 + 2*a^2*c^3/9 + a^2*c^2/3 + a*b^5/9 + 16*a*b^4*c/81 + a*b^4/3 + 17*a*b^3*c^2/27 + 4*a*b^3*c/27 + 19*a*b^2*c^3/27 + 14*a*b^2*c^2/27 + a*b^2*c/9 + 16*a*b*c^4/81 + 4*a*b*c^3/27 + a*b*c^2/9 + a*b*c/3 - 8*a*c^5/27 + a*c^4/9 + a*c^3/3 - 8*b^5*c/27 - 2*b^4*c^2/9 + b^4*c/9 - b^3*c^3/9 + 2*b^3*c^2/9 + b^3*c/3 - 2*b^2*c^4/27 + 4*b^2*c^3/9 + b^2*c^2/3 + b*c^5/9 + b*c^4/3) * hab
  have hn : 0 ≤ (a^6*c + a^5*b*c + a^5*b + a^5*c^2 + a^4*b^2 + a^4*b*c^2 + a^4*c^2 - a^4*c + a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - a^3*b + a^3*c^3 - a^3*c^2 + a^2*b^5 + a^2*b^4*c + a^2*b^4 - a^2*b^3*c - a^2*b^3 - 2*a^2*b^2*c^2 - a^2*b^2*c - a^2*b^2 - a^2*b*c^3 - a^2*b*c^2 + a^2*c^4 - a^2*c^2 + a*b^6 + a*b^5*c - a*b^4 - a*b^3*c^2 + a*b^2*c^4 - a*b^2*c^3 - a*b^2*c^2 + a*b*c^5 - a*b*c + a*c^5 - a*c^3 + b^5*c + b^4*c^2 + b^3*c^3 - b^3*c + b^2*c^5 + b^2*c^4 - b^2*c^3 - b^2*c^2 + b*c^6 - b*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^3 / (b^2 + b * c + a) + b^3 / (c^2 + c * a + b) + c^3 / (a^2 + a * b + c) ≥ 1) := @solution
#print axioms solution
