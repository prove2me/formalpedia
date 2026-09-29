-- Prove2me | solution 1 for WorkbookSource.base_27460
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:03.958762+00:00
-- url     : https://prove2.me/submissions/6851cab0-ba3e-4985-901b-eb49064f3769

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (3 * a + 2 * b + c) ^ 2 + 1 / (3 * b + 2 * c + a) ^ 2 + 1 / (3 * c + 2 * a + b) ^ 2) ≤ 1 / (4 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (36*a^6 + 104*a^5*b + 80*a^5*c + 189*a^4*b^2 + 82*a^4*b*c + 21*a^4*c^2 + 58*a^3*b^3 - 122*a^3*b^2*c - 266*a^3*b*c^2 + 58*a^3*c^3 + 21*a^2*b^4 - 266*a^2*b^3*c - 546*a^2*b^2*c^2 - 122*a^2*b*c^3 + 189*a^2*c^4 + 80*a*b^5 + 82*a*b^4*c - 122*a*b^3*c^2 - 266*a*b^2*c^3 + 82*a*b*c^4 + 104*a*c^5 + 36*b^6 + 104*b^5*c + 189*b^4*c^2 + 58*b^3*c^3 + 21*b^2*c^4 + 80*b*c^5 + 36*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2592 : ℝ) * a^4 * (b - a)^2 + (2592 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2592 : ℝ) * a^4 * (c - b)^2 + (6912 : ℝ) * a^3 * (b - a)^3 + (9504 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (9504 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (3456 : ℝ) * a^3 * (c - b)^3 + (6936 : ℝ) * a^2 * (b - a)^4 + (12144 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (13032 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (7824 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1752 : ℝ) * a^2 * (c - b)^4 + (3104 : ℝ) * a^1 * (b - a)^5 + (6668 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (7928 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (6088 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2524 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (400 : ℝ) * a^1 * (c - b)^5 + (524 : ℝ) * (b - a)^6 + (1356 : ℝ) * (b - a)^5 * (c - b)^1 + (1829 : ℝ) * (b - a)^4 * (c - b)^2 + (1662 : ℝ) * (b - a)^3 * (c - b)^3 + (961 : ℝ) * (b - a)^2 * (c - b)^4 + (296 : ℝ) * (b - a)^1 * (c - b)^5 + (36 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (36*a^6 + 104*a^5*b + 80*a^5*c + 189*a^4*b^2 + 82*a^4*b*c + 21*a^4*c^2 + 58*a^3*b^3 - 122*a^3*b^2*c - 266*a^3*b*c^2 + 58*a^3*c^3 + 21*a^2*b^4 - 266*a^2*b^3*c - 546*a^2*b^2*c^2 - 122*a^2*b*c^3 + 189*a^2*c^4 + 80*a*b^5 + 82*a*b^4*c - 122*a*b^3*c^2 - 266*a*b^2*c^3 + 82*a*b*c^4 + 104*a*c^5 + 36*b^6 + 104*b^5*c + 189*b^4*c^2 + 58*b^3*c^3 + 21*b^2*c^4 + 80*b*c^5 + 36*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2592 : ℝ) * a^4 * (c - a)^2 + (2592 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (2592 : ℝ) * a^4 * (b - c)^2 + (6912 : ℝ) * a^3 * (c - a)^3 + (11232 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (11232 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (3456 : ℝ) * a^3 * (b - c)^3 + (6936 : ℝ) * a^2 * (c - a)^4 + (15600 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (18216 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (9552 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1752 : ℝ) * a^2 * (b - c)^4 + (3104 : ℝ) * a^1 * (c - a)^5 + (8852 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (12296 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (8728 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2980 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (400 : ℝ) * a^1 * (b - c)^5 + (524 : ℝ) * (c - a)^6 + (1788 : ℝ) * (c - a)^5 * (b - c)^1 + (2909 : ℝ) * (c - a)^4 * (b - c)^2 + (2574 : ℝ) * (c - a)^3 * (b - c)^3 + (1249 : ℝ) * (c - a)^2 * (b - c)^4 + (320 : ℝ) * (c - a)^1 * (b - c)^5 + (36 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (36*a^6 + 104*a^5*b + 80*a^5*c + 189*a^4*b^2 + 82*a^4*b*c + 21*a^4*c^2 + 58*a^3*b^3 - 122*a^3*b^2*c - 266*a^3*b*c^2 + 58*a^3*c^3 + 21*a^2*b^4 - 266*a^2*b^3*c - 546*a^2*b^2*c^2 - 122*a^2*b*c^3 + 189*a^2*c^4 + 80*a*b^5 + 82*a*b^4*c - 122*a*b^3*c^2 - 266*a*b^2*c^3 + 82*a*b*c^4 + 104*a*c^5 + 36*b^6 + 104*b^5*c + 189*b^4*c^2 + 58*b^3*c^3 + 21*b^2*c^4 + 80*b*c^5 + 36*c^6) := by
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
  have hn : 0 ≤ (36*a^6 + 104*a^5*b + 80*a^5*c + 189*a^4*b^2 + 82*a^4*b*c + 21*a^4*c^2 + 58*a^3*b^3 - 122*a^3*b^2*c - 266*a^3*b*c^2 + 58*a^3*c^3 + 21*a^2*b^4 - 266*a^2*b^3*c - 546*a^2*b^2*c^2 - 122*a^2*b*c^3 + 189*a^2*c^4 + 80*a*b^5 + 82*a*b^4*c - 122*a*b^3*c^2 - 266*a*b^2*c^3 + 82*a*b*c^4 + 104*a*c^5 + 36*b^6 + 104*b^5*c + 189*b^4*c^2 + 58*b^3*c^3 + 21*b^2*c^4 + 80*b*c^5 + 36*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (3 * a + 2 * b + c) ^ 2 + 1 / (3 * b + 2 * c + a) ^ 2 + 1 / (3 * c + 2 * a + b) ^ 2) ≤ 1 / (4 * (a * b + b * c + c * a))) := @solution
#print axioms solution
