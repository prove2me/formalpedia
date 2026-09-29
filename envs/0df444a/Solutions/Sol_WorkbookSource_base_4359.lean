-- Prove2me | solution 1 for WorkbookSource.base_4359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:13.582534+00:00
-- url     : https://prove2.me/submissions/392f8933-83dd-4100-8221-a8503ab21fb0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2 + c^2) * (1/(a + 2 * c) + 1/(b + 2 * c)) ≥ a + b  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3 + 2*a^2*c - 4*a*b*c - 3*a*c^2 + b^3 + 2*b^2*c - 3*b*c^2 + 4*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^1 * (b - a)^2 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^1 * (c - b)^2 + (4 : ℝ) * (b - a)^3 + (8 : ℝ) * (b - a)^2 * (c - b)^1 + (9 : ℝ) * (b - a)^1 * (c - b)^2 + (4 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^3 + 2*a^2*c - 4*a*b*c - 3*a*c^2 + b^3 + 2*b^2*c - 3*b*c^2 + 4*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^1 * (c - a)^2 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (5 : ℝ) * a^1 * (b - c)^2 + (4 : ℝ) * (c - a)^3 + (4 : ℝ) * (c - a)^2 * (b - c)^1 + (5 : ℝ) * (c - a)^1 * (b - c)^2 + (1 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ c) (hord1 : c ≤ a) (hord2 : a ≤ b) : 0 ≤ (a^3 + 2*a^2*c - 4*a*b*c - 3*a*c^2 + b^3 + 2*b^2*c - 3*b*c^2 + 4*c^3) := by
    have hdiff1 : 0 ≤ (a - c) := by linarith
    have hdiff2 : 0 ≤ (b - a) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * c^1 * (a - c)^2 + (6 : ℝ) * c^1 * (a - c)^1 * (b - a)^1 + (5 : ℝ) * c^1 * (b - a)^2 + (2 : ℝ) * (a - c)^3 + (3 : ℝ) * (a - c)^2 * (b - a)^1 + (3 : ℝ) * (a - c)^1 * (b - a)^2 + (1 : ℝ) * (b - a)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3 + 2*a^2*c - 4*a*b*c - 3*a*c^2 + b^3 + 2*b^2*c - 3*b*c^2 + 4*c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux1 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3 + 2*a^2*c - 4*a*b*c - 3*a*c^2 + b^3 + 2*b^2*c - 3*b*c^2 + 4*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^2 + b^2 + c^2) * (1/(a + 2 * c) + 1/(b + 2 * c)) ≥ a + b) := @solution
#print axioms solution
