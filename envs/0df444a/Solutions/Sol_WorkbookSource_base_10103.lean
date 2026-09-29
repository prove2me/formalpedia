-- Prove2me | solution 1 for WorkbookSource.base_10103
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:44.070928+00:00
-- url     : https://prove2.me/submissions/1b16ea71-5173-4618-9278-22cb52153363

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (8 * a ^ 2 + b * c) + 2 / (8 * b ^ 2 + a * c) + 2 / (8 * c ^ 2 + a * b) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) - 3 / (a * b + b * c + a * c) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6*b^2 + 8*a^6*b*c + 16*a^6*c^2 - 64*a^5*b^3 + 154*a^5*b^2*c + 154*a^5*b*c^2 - 64*a^5*c^3 + 96*a^4*b^4 + 218*a^4*b^3*c - 1493*a^4*b^2*c^2 + 218*a^4*b*c^3 + 96*a^4*c^4 - 64*a^3*b^5 + 218*a^3*b^4*c + 741*a^3*b^3*c^2 + 741*a^3*b^2*c^3 + 218*a^3*b*c^4 - 64*a^3*c^5 + 16*a^2*b^6 + 154*a^2*b^5*c - 1493*a^2*b^4*c^2 + 741*a^2*b^3*c^3 - 1493*a^2*b^2*c^4 + 154*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^6*c + 154*a*b^5*c^2 + 218*a*b^4*c^3 + 218*a*b^3*c^4 + 154*a*b^2*c^5 + 8*a*b*c^6 + 16*b^6*c^2 - 64*b^5*c^3 + 96*b^4*c^4 - 64*b^3*c^5 + 16*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (675 : ℝ) * a^6 * (b - a)^2 + (675 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (675 : ℝ) * a^6 * (c - b)^2 + (3120 : ℝ) * a^5 * (b - a)^3 + (4680 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (3420 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (930 : ℝ) * a^5 * (c - b)^3 + (6110 : ℝ) * a^4 * (b - a)^4 + (12220 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (9705 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3595 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (635 : ℝ) * a^4 * (c - b)^4 + (6320 : ℝ) * a^3 * (b - a)^5 + (15800 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (15600 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (7600 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2320 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (420 : ℝ) * a^3 * (c - b)^5 + (3415 : ℝ) * a^2 * (b - a)^6 + (10245 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (12432 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (7789 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (2937 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (750 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (40 : ℝ) * a^2 * (c - b)^6 + (760 : ℝ) * a^1 * (b - a)^7 + (2660 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (3776 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (2790 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1172 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (298 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (16 : ℝ) * (b - a)^4 * (c - b)^4 + (32 : ℝ) * (b - a)^3 * (c - b)^5 + (16 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6*b^2 + 8*a^6*b*c + 16*a^6*c^2 - 64*a^5*b^3 + 154*a^5*b^2*c + 154*a^5*b*c^2 - 64*a^5*c^3 + 96*a^4*b^4 + 218*a^4*b^3*c - 1493*a^4*b^2*c^2 + 218*a^4*b*c^3 + 96*a^4*c^4 - 64*a^3*b^5 + 218*a^3*b^4*c + 741*a^3*b^3*c^2 + 741*a^3*b^2*c^3 + 218*a^3*b*c^4 - 64*a^3*c^5 + 16*a^2*b^6 + 154*a^2*b^5*c - 1493*a^2*b^4*c^2 + 741*a^2*b^3*c^3 - 1493*a^2*b^2*c^4 + 154*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^6*c + 154*a*b^5*c^2 + 218*a*b^4*c^3 + 218*a*b^3*c^4 + 154*a*b^2*c^5 + 8*a*b*c^6 + 16*b^6*c^2 - 64*b^5*c^3 + 96*b^4*c^4 - 64*b^3*c^5 + 16*b^2*c^6) := by
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
  have hn : 0 ≤ (16*a^6*b^2 + 8*a^6*b*c + 16*a^6*c^2 - 64*a^5*b^3 + 154*a^5*b^2*c + 154*a^5*b*c^2 - 64*a^5*c^3 + 96*a^4*b^4 + 218*a^4*b^3*c - 1493*a^4*b^2*c^2 + 218*a^4*b*c^3 + 96*a^4*c^4 - 64*a^3*b^5 + 218*a^3*b^4*c + 741*a^3*b^3*c^2 + 741*a^3*b^2*c^3 + 218*a^3*b*c^4 - 64*a^3*c^5 + 16*a^2*b^6 + 154*a^2*b^5*c - 1493*a^2*b^4*c^2 + 741*a^2*b^3*c^3 - 1493*a^2*b^2*c^4 + 154*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^6*c + 154*a*b^5*c^2 + 218*a*b^4*c^3 + 218*a*b^3*c^4 + 154*a*b^2*c^5 + 8*a*b*c^6 + 16*b^6*c^2 - 64*b^5*c^3 + 96*b^4*c^4 - 64*b^3*c^5 + 16*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 / (8 * a ^ 2 + b * c) + 2 / (8 * b ^ 2 + a * c) + 2 / (8 * c ^ 2 + a * b) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) - 3 / (a * b + b * c + a * c) ≥ 0) := @solution
#print axioms solution
