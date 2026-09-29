-- Prove2me | solution 1 for WorkbookSource.base_18429
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:38.983989+00:00
-- url     : https://prove2.me/submissions/ce5c6666-5dd9-41bb-b4f7-c4bb59b6ea7e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^4 + 5 * b^4) / (a * (a + 2 * b)) + (b^4 + 5 * c^4) / (b * (b + 2 * c)) + (c^4 + 5 * a^4) / (c * (c + 2 * a)) ≥ 2 * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 10*a^5*b^3 + 18*a^5*b^2*c - 4*a^5*b*c^2 - 8*a^4*b^3*c - 17*a^4*b^2*c^2 - 2*a^4*b*c^3 - 2*a^3*b^4*c - 12*a^3*b^3*c^2 - 12*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 - 4*a^2*b^5*c - 17*a^2*b^4*c^2 - 12*a^2*b^3*c^3 - 17*a^2*b^2*c^4 + 18*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 18*a*b^5*c^2 - 8*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (204 : ℝ) * a^6 * (b - a)^2 + (204 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (204 : ℝ) * a^6 * (c - b)^2 + (816 : ℝ) * a^5 * (b - a)^3 + (1032 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1032 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (408 : ℝ) * a^5 * (c - b)^3 + (1338 : ℝ) * a^4 * (b - a)^4 + (2036 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2034 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1336 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (318 : ℝ) * a^4 * (c - b)^4 + (1158 : ℝ) * a^3 * (b - a)^5 + (2056 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2024 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1620 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (722 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (114 : ℝ) * a^3 * (c - b)^5 + (561 : ℝ) * a^2 * (b - a)^6 + (1142 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1085 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (876 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (532 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (160 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (15 : ℝ) * a^2 * (c - b)^6 + (144 : ℝ) * a^1 * (b - a)^7 + (334 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (302 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (194 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (128 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (56 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (15 : ℝ) * (b - a)^8 + (40 : ℝ) * (b - a)^7 * (c - b)^1 + (35 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 10*a^5*b^3 + 18*a^5*b^2*c - 4*a^5*b*c^2 - 8*a^4*b^3*c - 17*a^4*b^2*c^2 - 2*a^4*b*c^3 - 2*a^3*b^4*c - 12*a^3*b^3*c^2 - 12*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 - 4*a^2*b^5*c - 17*a^2*b^4*c^2 - 12*a^2*b^3*c^3 - 17*a^2*b^2*c^4 + 18*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 18*a*b^5*c^2 - 8*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (204 : ℝ) * a^6 * (c - a)^2 + (204 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (204 : ℝ) * a^6 * (b - c)^2 + (816 : ℝ) * a^5 * (c - a)^3 + (1416 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (1416 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (408 : ℝ) * a^5 * (b - c)^3 + (1338 : ℝ) * a^4 * (c - a)^4 + (3316 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (3954 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (1976 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (318 : ℝ) * a^4 * (b - c)^4 + (1158 : ℝ) * a^3 * (c - a)^5 + (3734 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (5380 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (3696 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1120 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (114 : ℝ) * a^3 * (b - c)^5 + (561 : ℝ) * a^2 * (c - a)^6 + (2224 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (3790 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (3264 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (1409 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (272 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (15 : ℝ) * a^2 * (b - c)^6 + (144 : ℝ) * a^1 * (c - a)^7 + (674 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (1322 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (1346 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (732 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (198 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (20 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (15 : ℝ) * (c - a)^8 + (80 : ℝ) * (c - a)^7 * (b - c)^1 + (175 : ℝ) * (c - a)^6 * (b - c)^2 + (200 : ℝ) * (c - a)^5 * (b - c)^3 + (125 : ℝ) * (c - a)^4 * (b - c)^4 + (40 : ℝ) * (c - a)^3 * (b - c)^5 + (5 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 10*a^5*b^3 + 18*a^5*b^2*c - 4*a^5*b*c^2 - 8*a^4*b^3*c - 17*a^4*b^2*c^2 - 2*a^4*b*c^3 - 2*a^3*b^4*c - 12*a^3*b^3*c^2 - 12*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 - 4*a^2*b^5*c - 17*a^2*b^4*c^2 - 12*a^2*b^3*c^3 - 17*a^2*b^2*c^4 + 18*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 18*a*b^5*c^2 - 8*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3) := by
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
  have hn : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 10*a^5*b^3 + 18*a^5*b^2*c - 4*a^5*b*c^2 - 8*a^4*b^3*c - 17*a^4*b^2*c^2 - 2*a^4*b*c^3 - 2*a^3*b^4*c - 12*a^3*b^3*c^2 - 12*a^3*b^2*c^3 - 8*a^3*b*c^4 + 10*a^3*c^5 - 4*a^2*b^5*c - 17*a^2*b^4*c^2 - 12*a^2*b^3*c^3 - 17*a^2*b^2*c^4 + 18*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 18*a*b^5*c^2 - 8*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^4 + 5 * b^4) / (a * (a + 2 * b)) + (b^4 + 5 * c^4) / (b * (b + 2 * c)) + (c^4 + 5 * a^4) / (c * (c + 2 * a)) ≥ 2 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
