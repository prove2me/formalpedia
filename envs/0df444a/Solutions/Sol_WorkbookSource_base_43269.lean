-- Prove2me | solution 1 for WorkbookSource.base_43269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:11.941891+00:00
-- url     : https://prove2.me/submissions/845f6c4e-e7b5-404a-86f6-28c66409c1b3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (3 * a^2 + 3 * b^2 + 2 * c^2) + (b^2 + c * a) / (3 * b^2 + 3 * c^2 + 2 * a^2) + (c^2 + a * b) / (3 * c^2 + 3 * a^2 + 2 * b^2) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (30*a^6 - 24*a^5*b - 36*a^5*c + 83*a^4*b^2 - 24*a^4*b*c + 87*a^4*c^2 - 60*a^3*b^3 - 60*a^3*b^2*c - 52*a^3*b*c^2 - 60*a^3*c^3 + 87*a^2*b^4 - 52*a^2*b^3*c + 168*a^2*b^2*c^2 - 60*a^2*b*c^3 + 83*a^2*c^4 - 36*a*b^5 - 24*a*b^4*c - 60*a*b^3*c^2 - 52*a*b^2*c^3 - 24*a*b*c^4 - 24*a*c^5 + 30*b^6 - 24*b^5*c + 83*b^4*c^2 - 60*b^3*c^3 + 87*b^2*c^4 - 36*b*c^5 + 30*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * a^4 * (b - a)^2 + (256 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (256 : ℝ) * a^4 * (c - b)^2 + (672 : ℝ) * a^3 * (b - a)^3 + (968 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1000 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (352 : ℝ) * a^3 * (c - b)^3 + (776 : ℝ) * a^2 * (b - a)^4 + (1472 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1776 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1080 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (296 : ℝ) * a^2 * (c - b)^4 + (440 : ℝ) * a^1 * (b - a)^5 + (1034 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1460 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1196 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (570 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (120 : ℝ) * a^1 * (c - b)^5 + (110 : ℝ) * (b - a)^6 + (310 : ℝ) * (b - a)^5 * (c - b)^1 + (515 : ℝ) * (b - a)^4 * (c - b)^2 + (528 : ℝ) * (b - a)^3 * (c - b)^3 + (357 : ℝ) * (b - a)^2 * (c - b)^4 + (144 : ℝ) * (b - a)^1 * (c - b)^5 + (30 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (30*a^6 - 24*a^5*b - 36*a^5*c + 83*a^4*b^2 - 24*a^4*b*c + 87*a^4*c^2 - 60*a^3*b^3 - 60*a^3*b^2*c - 52*a^3*b*c^2 - 60*a^3*c^3 + 87*a^2*b^4 - 52*a^2*b^3*c + 168*a^2*b^2*c^2 - 60*a^2*b*c^3 + 83*a^2*c^4 - 36*a*b^5 - 24*a*b^4*c - 60*a*b^3*c^2 - 52*a*b^2*c^3 - 24*a*b*c^4 - 24*a*c^5 + 30*b^6 - 24*b^5*c + 83*b^4*c^2 - 60*b^3*c^3 + 87*b^2*c^4 - 36*b*c^5 + 30*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * a^4 * (c - a)^2 + (256 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (256 : ℝ) * a^4 * (b - c)^2 + (672 : ℝ) * a^3 * (c - a)^3 + (1048 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1080 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (352 : ℝ) * a^3 * (b - c)^3 + (776 : ℝ) * a^2 * (c - a)^4 + (1632 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (2016 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1160 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (296 : ℝ) * a^2 * (b - c)^4 + (440 : ℝ) * a^1 * (c - a)^5 + (1166 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1724 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1380 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (622 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (120 : ℝ) * a^1 * (b - c)^5 + (110 : ℝ) * (c - a)^6 + (350 : ℝ) * (c - a)^5 * (b - c)^1 + (615 : ℝ) * (c - a)^4 * (b - c)^2 + (632 : ℝ) * (c - a)^3 * (b - c)^3 + (413 : ℝ) * (c - a)^2 * (b - c)^4 + (156 : ℝ) * (c - a)^1 * (b - c)^5 + (30 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (30*a^6 - 24*a^5*b - 36*a^5*c + 83*a^4*b^2 - 24*a^4*b*c + 87*a^4*c^2 - 60*a^3*b^3 - 60*a^3*b^2*c - 52*a^3*b*c^2 - 60*a^3*c^3 + 87*a^2*b^4 - 52*a^2*b^3*c + 168*a^2*b^2*c^2 - 60*a^2*b*c^3 + 83*a^2*c^4 - 36*a*b^5 - 24*a*b^4*c - 60*a*b^3*c^2 - 52*a*b^2*c^3 - 24*a*b*c^4 - 24*a*c^5 + 30*b^6 - 24*b^5*c + 83*b^4*c^2 - 60*b^3*c^3 + 87*b^2*c^4 - 36*b*c^5 + 30*c^6) := by
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
  have hn : 0 ≤ (30*a^6 - 24*a^5*b - 36*a^5*c + 83*a^4*b^2 - 24*a^4*b*c + 87*a^4*c^2 - 60*a^3*b^3 - 60*a^3*b^2*c - 52*a^3*b*c^2 - 60*a^3*c^3 + 87*a^2*b^4 - 52*a^2*b^3*c + 168*a^2*b^2*c^2 - 60*a^2*b*c^3 + 83*a^2*c^4 - 36*a*b^5 - 24*a*b^4*c - 60*a*b^3*c^2 - 52*a*b^2*c^3 - 24*a*b*c^4 - 24*a*c^5 + 30*b^6 - 24*b^5*c + 83*b^4*c^2 - 60*b^3*c^3 + 87*b^2*c^4 - 36*b*c^5 + 30*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b * c) / (3 * a^2 + 3 * b^2 + 2 * c^2) + (b^2 + c * a) / (3 * b^2 + 3 * c^2 + 2 * a^2) + (c^2 + a * b) / (3 * c^2 + 3 * a^2 + 2 * b^2) ≤ 3 / 4) := @solution
#print axioms solution
