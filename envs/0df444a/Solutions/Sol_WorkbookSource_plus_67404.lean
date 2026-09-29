-- Prove2me | solution 1 for WorkbookSource.plus_67404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:52.691699+00:00
-- url     : https://prove2.me/submissions/6431851e-8d35-4758-b64c-09656b878805

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2 + 5 / 4) ≥ 6 * (a * b + b * c + c * a) / (a + b + c) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 + 16*a^5*b^2*c + 16*a^5*b*c^2 - 10*a^4*b^4 - 14*a^4*b^3*c - 14*a^4*b*c^3 - 10*a^4*c^4 - 14*a^3*b^4*c - 18*a^3*b^3*c^2 - 18*a^3*b^2*c^3 - 14*a^3*b*c^4 + 5*a^2*b^6 + 16*a^2*b^5*c - 18*a^2*b^3*c^3 + 16*a^2*b*c^5 + 5*a^2*c^6 + 14*a*b^6*c + 16*a*b^5*c^2 - 14*a*b^4*c^3 - 14*a*b^3*c^4 + 16*a*b^2*c^5 + 14*a*b*c^6 + 5*b^6*c^2 - 10*b^4*c^4 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * a^6 * (b - a)^2 + (224 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (224 : ℝ) * a^6 * (c - b)^2 + (800 : ℝ) * a^5 * (b - a)^3 + (1200 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1488 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (544 : ℝ) * a^5 * (c - b)^3 + (1112 : ℝ) * a^4 * (b - a)^4 + (2224 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (3416 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (2304 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (472 : ℝ) * a^4 * (c - b)^4 + (752 : ℝ) * a^3 * (b - a)^5 + (1880 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3568 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (3472 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1384 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (176 : ℝ) * a^3 * (c - b)^5 + (248 : ℝ) * a^2 * (b - a)^6 + (744 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1781 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2322 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1373 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (336 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (24 : ℝ) * a^2 * (c - b)^6 + (32 : ℝ) * a^1 * (b - a)^7 + (112 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (380 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (670 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (536 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (190 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (24 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (20 : ℝ) * (b - a)^6 * (c - b)^2 + (60 : ℝ) * (b - a)^5 * (c - b)^3 + (65 : ℝ) * (b - a)^4 * (c - b)^4 + (30 : ℝ) * (b - a)^3 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 + 16*a^5*b^2*c + 16*a^5*b*c^2 - 10*a^4*b^4 - 14*a^4*b^3*c - 14*a^4*b*c^3 - 10*a^4*c^4 - 14*a^3*b^4*c - 18*a^3*b^3*c^2 - 18*a^3*b^2*c^3 - 14*a^3*b*c^4 + 5*a^2*b^6 + 16*a^2*b^5*c - 18*a^2*b^3*c^3 + 16*a^2*b*c^5 + 5*a^2*c^6 + 14*a*b^6*c + 16*a*b^5*c^2 - 14*a*b^4*c^3 - 14*a*b^3*c^4 + 16*a*b^2*c^5 + 14*a*b*c^6 + 5*b^6*c^2 - 10*b^4*c^4 + 5*b^2*c^6) := by
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
  have hn : 0 ≤ (5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 + 16*a^5*b^2*c + 16*a^5*b*c^2 - 10*a^4*b^4 - 14*a^4*b^3*c - 14*a^4*b*c^3 - 10*a^4*c^4 - 14*a^3*b^4*c - 18*a^3*b^3*c^2 - 18*a^3*b^2*c^3 - 14*a^3*b*c^4 + 5*a^2*b^6 + 16*a^2*b^5*c - 18*a^2*b^3*c^3 + 16*a^2*b*c^5 + 5*a^2*c^6 + 14*a*b^6*c + 16*a*b^5*c^2 - 14*a*b^4*c^3 - 14*a*b^3*c^4 + 16*a*b^2*c^5 + 14*a*b*c^6 + 5*b^6*c^2 - 10*b^4*c^4 + 5*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2 + 5 / 4) ≥ 6 * (a * b + b * c + c * a) / (a + b + c) ^ 2) := @solution
#print axioms solution
