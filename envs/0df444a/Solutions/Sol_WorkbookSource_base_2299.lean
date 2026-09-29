-- Prove2me | solution 1 for WorkbookSource.base_2299
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:58:47.770187+00:00
-- url     : https://prove2.me/submissions/0b182985-aace-4fc6-8f17-d30aa53cbf69

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b^2) / (a^2 + b^2) * a + (b^2 - c^2) / (b^2 + c^2) * b + (c^2 - a^2) / (c^2 + a^2) * c ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^2 + a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^4*c^3 - b^3*c^4 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^5 * (b - a)^2 + (8 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^5 * (c - b)^2 + (28 : ℝ) * a^4 * (b - a)^3 + (36 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (32 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^4 * (c - b)^3 + (40 : ℝ) * a^3 * (b - a)^4 + (64 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (56 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (32 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^3 * (c - b)^4 + (30 : ℝ) * a^2 * (b - a)^5 + (60 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (56 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (14 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^6 + (30 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (33 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (24 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (11 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (b - a)^7 + (6 : ℝ) * (b - a)^6 * (c - b)^1 + (8 : ℝ) * (b - a)^5 * (c - b)^2 + (7 : ℝ) * (b - a)^4 * (c - b)^3 + (4 : ℝ) * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b^2 + a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^4*c^3 - b^3*c^4 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^5 * (c - a)^2 + (8 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^5 * (b - c)^2 + (28 : ℝ) * a^4 * (c - a)^3 + (48 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (44 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^4 * (b - c)^3 + (40 : ℝ) * a^3 * (c - a)^4 + (96 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (104 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (48 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (8 : ℝ) * a^3 * (b - c)^4 + (30 : ℝ) * a^2 * (c - a)^5 + (90 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (116 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (72 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^2 * (b - c)^5 + (12 : ℝ) * a^1 * (c - a)^6 + (42 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (63 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (48 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (17 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (2 : ℝ) * (c - a)^7 + (8 : ℝ) * (c - a)^6 * (b - c)^1 + (14 : ℝ) * (c - a)^5 * (b - c)^2 + (13 : ℝ) * (c - a)^4 * (b - c)^3 + (6 : ℝ) * (c - a)^3 * (b - c)^4 + (1 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^2 + a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^4*c^3 - b^3*c^4 + b^2*c^5) := by
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
  have hn : 0 ≤ (a^5*b^2 + a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^4*c^3 - b^3*c^4 + b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 - b^2) / (a^2 + b^2) * a + (b^2 - c^2) / (b^2 + c^2) * b + (c^2 - a^2) / (c^2 + a^2) * c ≥ 0) := @solution
#print axioms solution
