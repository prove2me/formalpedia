-- Prove2me | solution 1 for WorkbookSource.base_36205
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:21.572019+00:00
-- url     : https://prove2.me/submissions/06faf0fd-d997-46fd-a1e5-c997dcdc0758

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 16 * ((a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 13  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (19*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + 7*a^5*b^3 - 11*a^5*b^2*c - 11*a^5*b*c^2 + 7*a^5*c^3 + 24*a^4*b^4 + a^4*b^3*c - 46*a^4*b^2*c^2 + a^4*b*c^3 + 24*a^4*c^4 + 7*a^3*b^5 + a^3*b^4*c + a^3*b*c^4 + 7*a^3*c^5 + 3*a^2*b^6 - 11*a^2*b^5*c - 46*a^2*b^4*c^2 - 46*a^2*b^2*c^4 - 11*a^2*b*c^5 + 19*a^2*c^6 + 6*a*b^6*c - 11*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 11*a*b^2*c^5 + 6*a*b*c^6 + 19*b^6*c^2 + 7*b^5*c^3 + 24*b^4*c^4 + 7*b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (320 : ℝ) * a^6 * (b - a)^2 + (320 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (320 : ℝ) * a^6 * (c - b)^2 + (1408 : ℝ) * a^5 * (b - a)^3 + (1920 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1536 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (512 : ℝ) * a^5 * (c - b)^3 + (2624 : ℝ) * a^4 * (b - a)^4 + (4608 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (3712 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1728 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (384 : ℝ) * a^4 * (c - b)^4 + (2656 : ℝ) * a^3 * (b - a)^5 + (5760 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (5248 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (2752 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (928 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (160 : ℝ) * a^3 * (c - b)^5 + (1532 : ℝ) * a^2 * (b - a)^6 + (3972 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (4228 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2476 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (916 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (228 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (28 : ℝ) * a^2 * (c - b)^6 + (472 : ℝ) * a^1 * (b - a)^7 + (1428 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1772 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1180 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (452 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (100 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (60 : ℝ) * (b - a)^8 + (208 : ℝ) * (b - a)^7 * (c - b)^1 + (299 : ℝ) * (b - a)^6 * (c - b)^2 + (233 : ℝ) * (b - a)^5 * (c - b)^3 + (104 : ℝ) * (b - a)^4 * (c - b)^4 + (25 : ℝ) * (b - a)^3 * (c - b)^5 + (3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (19*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + 7*a^5*b^3 - 11*a^5*b^2*c - 11*a^5*b*c^2 + 7*a^5*c^3 + 24*a^4*b^4 + a^4*b^3*c - 46*a^4*b^2*c^2 + a^4*b*c^3 + 24*a^4*c^4 + 7*a^3*b^5 + a^3*b^4*c + a^3*b*c^4 + 7*a^3*c^5 + 3*a^2*b^6 - 11*a^2*b^5*c - 46*a^2*b^4*c^2 - 46*a^2*b^2*c^4 - 11*a^2*b*c^5 + 19*a^2*c^6 + 6*a*b^6*c - 11*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 11*a*b^2*c^5 + 6*a*b*c^6 + 19*b^6*c^2 + 7*b^5*c^3 + 24*b^4*c^4 + 7*b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (320 : ℝ) * a^6 * (c - a)^2 + (320 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (320 : ℝ) * a^6 * (b - c)^2 + (1408 : ℝ) * a^5 * (c - a)^3 + (2304 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (1920 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (512 : ℝ) * a^5 * (b - c)^3 + (2624 : ℝ) * a^4 * (c - a)^4 + (5888 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (5632 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (2368 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (384 : ℝ) * a^4 * (b - c)^4 + (2656 : ℝ) * a^3 * (c - a)^5 + (7520 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (8768 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (4992 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1408 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (160 : ℝ) * a^3 * (b - c)^5 + (1532 : ℝ) * a^2 * (c - a)^6 + (5220 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (7348 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (5356 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (2116 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (420 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (28 : ℝ) * a^2 * (b - c)^6 + (472 : ℝ) * a^1 * (c - a)^7 + (1876 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (3116 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (2780 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1412 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (388 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (44 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (60 : ℝ) * (c - a)^8 + (272 : ℝ) * (c - a)^7 * (b - c)^1 + (523 : ℝ) * (c - a)^6 * (b - c)^2 + (553 : ℝ) * (c - a)^5 * (b - c)^3 + (344 : ℝ) * (c - a)^4 * (b - c)^4 + (121 : ℝ) * (c - a)^3 * (b - c)^5 + (19 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (19*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + 7*a^5*b^3 - 11*a^5*b^2*c - 11*a^5*b*c^2 + 7*a^5*c^3 + 24*a^4*b^4 + a^4*b^3*c - 46*a^4*b^2*c^2 + a^4*b*c^3 + 24*a^4*c^4 + 7*a^3*b^5 + a^3*b^4*c + a^3*b*c^4 + 7*a^3*c^5 + 3*a^2*b^6 - 11*a^2*b^5*c - 46*a^2*b^4*c^2 - 46*a^2*b^2*c^4 - 11*a^2*b*c^5 + 19*a^2*c^6 + 6*a*b^6*c - 11*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 11*a*b^2*c^5 + 6*a*b*c^6 + 19*b^6*c^2 + 7*b^5*c^3 + 24*b^4*c^4 + 7*b^3*c^5 + 3*b^2*c^6) := by
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
  have hn : 0 ≤ (19*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + 7*a^5*b^3 - 11*a^5*b^2*c - 11*a^5*b*c^2 + 7*a^5*c^3 + 24*a^4*b^4 + a^4*b^3*c - 46*a^4*b^2*c^2 + a^4*b*c^3 + 24*a^4*c^4 + 7*a^3*b^5 + a^3*b^4*c + a^3*b*c^4 + 7*a^3*c^5 + 3*a^2*b^6 - 11*a^2*b^5*c - 46*a^2*b^4*c^2 - 46*a^2*b^2*c^4 - 11*a^2*b*c^5 + 19*a^2*c^6 + 6*a*b^6*c - 11*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 11*a*b^2*c^5 + 6*a*b*c^6 + 19*b^6*c^2 + 7*b^5*c^3 + 24*b^4*c^4 + 7*b^3*c^5 + 3*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 16 * ((a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 13) := @solution
#print axioms solution
