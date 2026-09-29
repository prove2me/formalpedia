-- Prove2me | solution 1 for WorkbookSource.plus_67114
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:46:54.9582+00:00
-- url     : https://prove2.me/submissions/616659ab-b992-4043-bc4b-836c391c8b3c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b^2 + b * c + c^2) + b^2 / (c^2 + c * a + a^2) + c^2 / (a^2 + a * b + b^2)) ≥ 1 / 9 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 8 / 9   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^7*b + 9*a^7*c + 8*a^6*b^2 + 26*a^6*b*c + 8*a^6*c^2 + 9*a^5*b^2*c + 9*a^5*b*c^2 - 10*a^4*b^4 - 17*a^4*b^3*c - 18*a^4*b^2*c^2 - 17*a^4*b*c^3 - 10*a^4*c^4 - 17*a^3*b^4*c - 16*a^3*b^3*c^2 - 16*a^3*b^2*c^3 - 17*a^3*b*c^4 + 8*a^2*b^6 + 9*a^2*b^5*c - 18*a^2*b^4*c^2 - 16*a^2*b^3*c^3 - 18*a^2*b^2*c^4 + 9*a^2*b*c^5 + 8*a^2*c^6 + 9*a*b^7 + 26*a*b^6*c + 9*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 9*a*b^2*c^5 + 26*a*b*c^6 + 9*a*c^7 + 9*b^7*c + 8*b^6*c^2 - 10*b^4*c^4 + 8*b^2*c^6 + 9*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (540 : ℝ) * a^6 * (b - a)^2 + (540 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (540 : ℝ) * a^6 * (c - b)^2 + (1944 : ℝ) * a^5 * (b - a)^3 + (2916 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (3564 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1296 : ℝ) * a^5 * (c - b)^3 + (2898 : ℝ) * a^4 * (b - a)^4 + (5796 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (8694 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (5796 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1278 : ℝ) * a^4 * (c - b)^4 + (2304 : ℝ) * a^3 * (b - a)^5 + (5760 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (10368 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (9792 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (4176 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (648 : ℝ) * a^3 * (c - b)^5 + (1032 : ℝ) * a^2 * (b - a)^6 + (3096 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (6516 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (7872 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (4896 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (1476 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (168 : ℝ) * a^2 * (c - b)^6 + (246 : ℝ) * a^1 * (b - a)^7 + (861 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (2067 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (3015 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (2433 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1065 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (231 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (18 : ℝ) * a^1 * (c - b)^7 + (24 : ℝ) * (b - a)^8 + (96 : ℝ) * (b - a)^7 * (c - b)^1 + (257 : ℝ) * (b - a)^6 * (c - b)^2 + (435 : ℝ) * (b - a)^5 * (c - b)^3 + (425 : ℝ) * (b - a)^4 * (c - b)^4 + (237 : ℝ) * (b - a)^3 * (c - b)^5 + (71 : ℝ) * (b - a)^2 * (c - b)^6 + (9 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^7*b + 9*a^7*c + 8*a^6*b^2 + 26*a^6*b*c + 8*a^6*c^2 + 9*a^5*b^2*c + 9*a^5*b*c^2 - 10*a^4*b^4 - 17*a^4*b^3*c - 18*a^4*b^2*c^2 - 17*a^4*b*c^3 - 10*a^4*c^4 - 17*a^3*b^4*c - 16*a^3*b^3*c^2 - 16*a^3*b^2*c^3 - 17*a^3*b*c^4 + 8*a^2*b^6 + 9*a^2*b^5*c - 18*a^2*b^4*c^2 - 16*a^2*b^3*c^3 - 18*a^2*b^2*c^4 + 9*a^2*b*c^5 + 8*a^2*c^6 + 9*a*b^7 + 26*a*b^6*c + 9*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 9*a*b^2*c^5 + 26*a*b*c^6 + 9*a*c^7 + 9*b^7*c + 8*b^6*c^2 - 10*b^4*c^4 + 8*b^2*c^6 + 9*b*c^7) := by
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
  have hn : 0 ≤ (9*a^7*b + 9*a^7*c + 8*a^6*b^2 + 26*a^6*b*c + 8*a^6*c^2 + 9*a^5*b^2*c + 9*a^5*b*c^2 - 10*a^4*b^4 - 17*a^4*b^3*c - 18*a^4*b^2*c^2 - 17*a^4*b*c^3 - 10*a^4*c^4 - 17*a^3*b^4*c - 16*a^3*b^3*c^2 - 16*a^3*b^2*c^3 - 17*a^3*b*c^4 + 8*a^2*b^6 + 9*a^2*b^5*c - 18*a^2*b^4*c^2 - 16*a^2*b^3*c^3 - 18*a^2*b^2*c^4 + 9*a^2*b*c^5 + 8*a^2*c^6 + 9*a*b^7 + 26*a*b^6*c + 9*a*b^5*c^2 - 17*a*b^4*c^3 - 17*a*b^3*c^4 + 9*a*b^2*c^5 + 26*a*b*c^6 + 9*a*c^7 + 9*b^7*c + 8*b^6*c^2 - 10*b^4*c^4 + 8*b^2*c^6 + 9*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (b^2 + b * c + c^2) + b^2 / (c^2 + c * a + a^2) + c^2 / (a^2 + a * b + b^2)) ≥ 1 / 9 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 8 / 9) := @solution
#print axioms solution
