-- Prove2me | solution 1 for WorkbookSource.base_20232
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:29.712677+00:00
-- url     : https://prove2.me/submissions/fbba6fd8-f87c-4a0d-8e3f-584b8d89f8cf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) ≥ a ^ 2 / (a ^ 2 + a * b + b * c) + b ^ 2 / (b ^ 2 + b * c + a * c) + c ^ 2 / (c ^ 2 + a * c + a * b) + 1 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b*c + 5*a^6*c^2 + 5*a^5*b^3 + 10*a^5*b^2*c - 4*a^4*b^4 - 9*a^4*b^3*c - 6*a^4*b^2*c^2 - 4*a^4*c^4 - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 - 9*a^3*b*c^4 + 5*a^3*c^5 + 5*a^2*b^6 - 6*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a*b^6*c + 10*a*b^5*c^2 - 9*a*b^4*c^3 + 5*a*b*c^6 + 5*b^5*c^3 - 4*b^4*c^4 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (111 : ℝ) * a^6 * (b - a)^2 + (111 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (111 : ℝ) * a^6 * (c - b)^2 + (424 : ℝ) * a^5 * (b - a)^3 + (642 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (702 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (242 : ℝ) * a^5 * (c - b)^3 + (657 : ℝ) * a^4 * (b - a)^4 + (1334 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1696 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1019 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (202 : ℝ) * a^4 * (c - b)^4 + (533 : ℝ) * a^3 * (b - a)^5 + (1374 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2032 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1654 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (613 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (75 : ℝ) * a^3 * (c - b)^5 + (242 : ℝ) * a^2 * (b - a)^6 + (773 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1320 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1324 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (695 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (160 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (10 : ℝ) * a^2 * (c - b)^6 + (59 : ℝ) * a^1 * (b - a)^7 + (231 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (454 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (536 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (359 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (120 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (6 : ℝ) * (b - a)^8 + (29 : ℝ) * (b - a)^7 * (c - b)^1 + (66 : ℝ) * (b - a)^6 * (c - b)^2 + (89 : ℝ) * (b - a)^5 * (c - b)^3 + (71 : ℝ) * (b - a)^4 * (c - b)^4 + (30 : ℝ) * (b - a)^3 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (5*a^6*b*c + 5*a^6*c^2 + 5*a^5*b^3 + 10*a^5*b^2*c - 4*a^4*b^4 - 9*a^4*b^3*c - 6*a^4*b^2*c^2 - 4*a^4*c^4 - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 - 9*a^3*b*c^4 + 5*a^3*c^5 + 5*a^2*b^6 - 6*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a*b^6*c + 10*a*b^5*c^2 - 9*a*b^4*c^3 + 5*a*b*c^6 + 5*b^5*c^3 - 4*b^4*c^4 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (111 : ℝ) * a^6 * (c - a)^2 + (111 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (111 : ℝ) * a^6 * (b - c)^2 + (424 : ℝ) * a^5 * (c - a)^3 + (630 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (690 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (242 : ℝ) * a^5 * (b - c)^3 + (657 : ℝ) * a^4 * (c - a)^4 + (1294 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1636 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (999 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (202 : ℝ) * a^4 * (b - c)^4 + (533 : ℝ) * a^3 * (c - a)^5 + (1291 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (1866 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1528 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (570 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (75 : ℝ) * a^3 * (b - c)^5 + (242 : ℝ) * a^2 * (c - a)^6 + (679 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (1085 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (1066 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (543 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (125 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (10 : ℝ) * a^2 * (b - c)^6 + (59 : ℝ) * a^1 * (c - a)^7 + (182 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (307 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (334 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (200 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (55 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (6 : ℝ) * (c - a)^8 + (19 : ℝ) * (c - a)^7 * (b - c)^1 + (31 : ℝ) * (c - a)^6 * (b - c)^2 + (34 : ℝ) * (c - a)^5 * (b - c)^3 + (21 : ℝ) * (c - a)^4 * (b - c)^4 + (5 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b*c + 5*a^6*c^2 + 5*a^5*b^3 + 10*a^5*b^2*c - 4*a^4*b^4 - 9*a^4*b^3*c - 6*a^4*b^2*c^2 - 4*a^4*c^4 - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 - 9*a^3*b*c^4 + 5*a^3*c^5 + 5*a^2*b^6 - 6*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a*b^6*c + 10*a*b^5*c^2 - 9*a*b^4*c^3 + 5*a*b*c^6 + 5*b^5*c^3 - 4*b^4*c^4 + 5*b^2*c^6) := by
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
  have hn : 0 ≤ (5*a^6*b*c + 5*a^6*c^2 + 5*a^5*b^3 + 10*a^5*b^2*c - 4*a^4*b^4 - 9*a^4*b^3*c - 6*a^4*b^2*c^2 - 4*a^4*c^4 - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 - 9*a^3*b*c^4 + 5*a^3*c^5 + 5*a^2*b^6 - 6*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a*b^6*c + 10*a*b^5*c^2 - 9*a*b^4*c^3 + 5*a*b*c^6 + 5*b^5*c^3 - 4*b^4*c^4 + 5*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (5 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) ≥ a ^ 2 / (a ^ 2 + a * b + b * c) + b ^ 2 / (b ^ 2 + b * c + a * c) + c ^ 2 / (c ^ 2 + a * c + a * b) + 1 / 4) := @solution
#print axioms solution
