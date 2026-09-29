-- Prove2me | solution 1 for WorkbookSource.base_56685
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:05.542844+00:00
-- url     : https://prove2.me/submissions/1f0f91c9-6f9e-4d79-a430-3b38d268bc79

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (6 * a + 5 * b + c) * (c - b) / (a * b * (3 * a + 2 * b + c) ^ 2) + (6 * b + 5 * c + a) * (a - c) / (b * c * (3 * b + 2 * c + a) ^ 2) + (6 * c + 5 * a + b) * (b - a) / (c * a * (3 * c + 2 * a + b) ^ 2) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (36*a^7 + 255*a^6*b + 276*a^6*c + 283*a^5*b^2 + 862*a^5*b*c + 529*a^5*c^2 - 46*a^4*b^3 + 16*a^4*b^2*c + 337*a^4*b*c^2 + 206*a^4*c^3 + 206*a^3*b^4 - 862*a^3*b^3*c - 1892*a^3*b^2*c^2 - 862*a^3*b*c^3 - 46*a^3*c^4 + 529*a^2*b^5 + 337*a^2*b^4*c - 1892*a^2*b^3*c^2 - 1892*a^2*b^2*c^3 + 16*a^2*b*c^4 + 283*a^2*c^5 + 276*a*b^6 + 862*a*b^5*c + 16*a*b^4*c^2 - 862*a*b^3*c^3 + 337*a*b^2*c^4 + 862*a*b*c^5 + 255*a*c^6 + 36*b^7 + 255*b^6*c + 283*b^5*c^2 - 46*b^4*c^3 + 206*b^3*c^4 + 529*b^2*c^5 + 276*b*c^6 + 36*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (15552 : ℝ) * a^5 * (b - a)^2 + (15552 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (15552 : ℝ) * a^5 * (c - b)^2 + (50544 : ℝ) * a^4 * (b - a)^3 + (79056 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (82944 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (27216 : ℝ) * a^4 * (c - b)^3 + (64764 : ℝ) * a^3 * (b - a)^4 + (138168 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (168372 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (94968 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (18108 : ℝ) * a^3 * (c - b)^4 + (40932 : ℝ) * a^2 * (b - a)^5 + (110736 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (158616 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (120708 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (43128 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (5616 : ℝ) * a^2 * (c - b)^5 + (12771 : ℝ) * a^1 * (b - a)^6 + (41856 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (69732 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (65598 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (33225 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (8274 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (783 : ℝ) * a^1 * (c - b)^6 + (1575 : ℝ) * (b - a)^7 + (6060 : ℝ) * (b - a)^6 * (c - b)^1 + (11567 : ℝ) * (b - a)^5 * (c - b)^2 + (12848 : ℝ) * (b - a)^4 * (c - b)^3 + (8251 : ℝ) * (b - a)^3 * (c - b)^4 + (2941 : ℝ) * (b - a)^2 * (c - b)^5 + (528 : ℝ) * (b - a)^1 * (c - b)^6 + (36 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (36*a^7 + 255*a^6*b + 276*a^6*c + 283*a^5*b^2 + 862*a^5*b*c + 529*a^5*c^2 - 46*a^4*b^3 + 16*a^4*b^2*c + 337*a^4*b*c^2 + 206*a^4*c^3 + 206*a^3*b^4 - 862*a^3*b^3*c - 1892*a^3*b^2*c^2 - 862*a^3*b*c^3 - 46*a^3*c^4 + 529*a^2*b^5 + 337*a^2*b^4*c - 1892*a^2*b^3*c^2 - 1892*a^2*b^2*c^3 + 16*a^2*b*c^4 + 283*a^2*c^5 + 276*a*b^6 + 862*a*b^5*c + 16*a*b^4*c^2 - 862*a*b^3*c^3 + 337*a*b^2*c^4 + 862*a*b*c^5 + 255*a*c^6 + 36*b^7 + 255*b^6*c + 283*b^5*c^2 - 46*b^4*c^3 + 206*b^3*c^4 + 529*b^2*c^5 + 276*b*c^6 + 36*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (15552 : ℝ) * a^5 * (c - a)^2 + (15552 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (15552 : ℝ) * a^5 * (b - c)^2 + (50544 : ℝ) * a^4 * (c - a)^3 + (72576 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (76464 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (27216 : ℝ) * a^4 * (b - c)^3 + (64764 : ℝ) * a^3 * (c - a)^4 + (120888 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (142452 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (86328 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (18108 : ℝ) * a^3 * (b - c)^4 + (40932 : ℝ) * a^2 * (c - a)^5 + (93924 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (124992 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (100044 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (39276 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (5616 : ℝ) * a^2 * (b - c)^5 + (12771 : ℝ) * a^1 * (c - a)^6 + (34770 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (52017 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (50190 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (27828 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (7656 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (783 : ℝ) * a^1 * (b - c)^6 + (1575 : ℝ) * (c - a)^7 + (4965 : ℝ) * (c - a)^6 * (b - c)^1 + (8282 : ℝ) * (c - a)^5 * (b - c)^2 + (9212 : ℝ) * (c - a)^4 * (b - c)^3 + (6454 : ℝ) * (c - a)^3 * (b - c)^4 + (2569 : ℝ) * (c - a)^2 * (b - c)^5 + (507 : ℝ) * (c - a)^1 * (b - c)^6 + (36 : ℝ) * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (36*a^7 + 255*a^6*b + 276*a^6*c + 283*a^5*b^2 + 862*a^5*b*c + 529*a^5*c^2 - 46*a^4*b^3 + 16*a^4*b^2*c + 337*a^4*b*c^2 + 206*a^4*c^3 + 206*a^3*b^4 - 862*a^3*b^3*c - 1892*a^3*b^2*c^2 - 862*a^3*b*c^3 - 46*a^3*c^4 + 529*a^2*b^5 + 337*a^2*b^4*c - 1892*a^2*b^3*c^2 - 1892*a^2*b^2*c^3 + 16*a^2*b*c^4 + 283*a^2*c^5 + 276*a*b^6 + 862*a*b^5*c + 16*a*b^4*c^2 - 862*a*b^3*c^3 + 337*a*b^2*c^4 + 862*a*b*c^5 + 255*a*c^6 + 36*b^7 + 255*b^6*c + 283*b^5*c^2 - 46*b^4*c^3 + 206*b^3*c^4 + 529*b^2*c^5 + 276*b*c^6 + 36*c^7) := by
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
  have hn : 0 ≤ (36*a^7 + 255*a^6*b + 276*a^6*c + 283*a^5*b^2 + 862*a^5*b*c + 529*a^5*c^2 - 46*a^4*b^3 + 16*a^4*b^2*c + 337*a^4*b*c^2 + 206*a^4*c^3 + 206*a^3*b^4 - 862*a^3*b^3*c - 1892*a^3*b^2*c^2 - 862*a^3*b*c^3 - 46*a^3*c^4 + 529*a^2*b^5 + 337*a^2*b^4*c - 1892*a^2*b^3*c^2 - 1892*a^2*b^2*c^3 + 16*a^2*b*c^4 + 283*a^2*c^5 + 276*a*b^6 + 862*a*b^5*c + 16*a*b^4*c^2 - 862*a*b^3*c^3 + 337*a*b^2*c^4 + 862*a*b*c^5 + 255*a*c^6 + 36*b^7 + 255*b^6*c + 283*b^5*c^2 - 46*b^4*c^3 + 206*b^3*c^4 + 529*b^2*c^5 + 276*b*c^6 + 36*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (6 * a + 5 * b + c) * (c - b) / (a * b * (3 * a + 2 * b + c) ^ 2) + (6 * b + 5 * c + a) * (a - c) / (b * c * (3 * b + 2 * c + a) ^ 2) + (6 * c + 5 * a + b) * (b - a) / (c * a * (3 * c + 2 * a + b) ^ 2) ≥ 0) := @solution
#print axioms solution
