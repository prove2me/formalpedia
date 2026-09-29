-- Prove2me | solution 1 for WorkbookSource.plus_57739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:09.560967+00:00
-- url     : https://prove2.me/submissions/d10cdcd1-fdb9-4b47-ac92-812fd90c9610

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (5 * a^2 + 2 * a * b + b^2) + b^3 / (5 * b^2 + 2 * b * c + c^2) + c^3 / (5 * c^2 + 2 * c * a + a^2)) ≥ (a + b + c) / 8   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (15*a^5*b^2 + 6*a^5*b*c + 3*a^5*c^2 + 5*a^4*b^3 - 9*a^4*b^2*c - 5*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c - 10*a^3*b^2*c^2 - 6*a^3*b*c^3 + 5*a^3*c^4 + 3*a^2*b^5 - 5*a^2*b^4*c - 10*a^2*b^3*c^2 - 10*a^2*b^2*c^3 - 9*a^2*b*c^4 + 15*a^2*c^5 + 6*a*b^5*c - 9*a*b^4*c^2 - 6*a*b^3*c^3 - 5*a*b^2*c^4 + 6*a*b*c^5 + 15*b^5*c^2 + 5*b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (128 : ℝ) * a^5 * (b - a)^2 + (128 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (128 : ℝ) * a^5 * (c - b)^2 + (448 : ℝ) * a^4 * (b - a)^3 + (576 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (512 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (192 : ℝ) * a^4 * (c - b)^3 + (624 : ℝ) * a^3 * (b - a)^4 + (992 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (848 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (480 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (112 : ℝ) * a^3 * (c - b)^4 + (440 : ℝ) * a^2 * (b - a)^5 + (844 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (728 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (440 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (164 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^2 * (c - b)^5 + (160 : ℝ) * a^1 * (b - a)^6 + (364 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (333 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (190 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (73 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (24 : ℝ) * (b - a)^7 + (64 : ℝ) * (b - a)^6 * (c - b)^1 + (66 : ℝ) * (b - a)^5 * (c - b)^2 + (39 : ℝ) * (b - a)^4 * (c - b)^3 + (16 : ℝ) * (b - a)^3 * (c - b)^4 + (3 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (15*a^5*b^2 + 6*a^5*b*c + 3*a^5*c^2 + 5*a^4*b^3 - 9*a^4*b^2*c - 5*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c - 10*a^3*b^2*c^2 - 6*a^3*b*c^3 + 5*a^3*c^4 + 3*a^2*b^5 - 5*a^2*b^4*c - 10*a^2*b^3*c^2 - 10*a^2*b^2*c^3 - 9*a^2*b*c^4 + 15*a^2*c^5 + 6*a*b^5*c - 9*a*b^4*c^2 - 6*a*b^3*c^3 - 5*a*b^2*c^4 + 6*a*b*c^5 + 15*b^5*c^2 + 5*b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (128 : ℝ) * a^5 * (c - a)^2 + (128 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (128 : ℝ) * a^5 * (b - c)^2 + (448 : ℝ) * a^4 * (c - a)^3 + (768 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (704 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (192 : ℝ) * a^4 * (b - c)^3 + (624 : ℝ) * a^3 * (c - a)^4 + (1504 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (1616 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (736 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (112 : ℝ) * a^3 * (b - c)^4 + (440 : ℝ) * a^2 * (c - a)^5 + (1356 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (1752 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (1080 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (292 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (24 : ℝ) * a^2 * (b - c)^5 + (160 : ℝ) * a^1 * (c - a)^6 + (596 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (913 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (702 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (261 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (36 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (24 : ℝ) * (c - a)^7 + (104 : ℝ) * (c - a)^6 * (b - c)^1 + (186 : ℝ) * (c - a)^5 * (b - c)^2 + (171 : ℝ) * (c - a)^4 * (b - c)^3 + (80 : ℝ) * (c - a)^3 * (b - c)^4 + (15 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (15*a^5*b^2 + 6*a^5*b*c + 3*a^5*c^2 + 5*a^4*b^3 - 9*a^4*b^2*c - 5*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c - 10*a^3*b^2*c^2 - 6*a^3*b*c^3 + 5*a^3*c^4 + 3*a^2*b^5 - 5*a^2*b^4*c - 10*a^2*b^3*c^2 - 10*a^2*b^2*c^3 - 9*a^2*b*c^4 + 15*a^2*c^5 + 6*a*b^5*c - 9*a*b^4*c^2 - 6*a*b^3*c^3 - 5*a*b^2*c^4 + 6*a*b*c^5 + 15*b^5*c^2 + 5*b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
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
  have hn : 0 ≤ (15*a^5*b^2 + 6*a^5*b*c + 3*a^5*c^2 + 5*a^4*b^3 - 9*a^4*b^2*c - 5*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c - 10*a^3*b^2*c^2 - 6*a^3*b*c^3 + 5*a^3*c^4 + 3*a^2*b^5 - 5*a^2*b^4*c - 10*a^2*b^3*c^2 - 10*a^2*b^2*c^3 - 9*a^2*b*c^4 + 15*a^2*c^5 + 6*a*b^5*c - 9*a*b^4*c^2 - 6*a*b^3*c^3 - 5*a*b^2*c^4 + 6*a*b*c^5 + 15*b^5*c^2 + 5*b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (5 * a^2 + 2 * a * b + b^2) + b^3 / (5 * b^2 + 2 * b * c + c^2) + c^3 / (5 * c^2 + 2 * c * a + a^2)) ≥ (a + b + c) / 8) := @solution
#print axioms solution
