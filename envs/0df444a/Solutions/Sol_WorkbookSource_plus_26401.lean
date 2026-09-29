-- Prove2me | solution 1 for WorkbookSource.plus_26401
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:04.66865+00:00
-- url     : https://prove2.me/submissions/1e0a7729-76fe-4155-90c1-66886cc4c3a6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^4 + b^4 + c^4 ≥ 2 * b * c * (a - b) * (a - c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4 - 2*a^2*b*c + 2*a*b^2*c + 2*a*b*c^2 + b^4 - 2*b^2*c^2 + c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^4 + (8 : ℝ) * a^3 * (b - a)^1 + (4 : ℝ) * a^3 * (c - b)^1 + (10 : ℝ) * a^2 * (b - a)^2 + (10 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^2 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^3 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^1 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^2 + (4 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (a^4 - 2*a^2*b*c + 2*a*b^2*c + 2*a*b*c^2 + b^4 - 2*b^2*c^2 + c^4) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * b^4 + (8 : ℝ) * b^3 * (a - b)^1 + (4 : ℝ) * b^3 * (c - a)^1 + (12 : ℝ) * b^2 * (a - b)^2 + (14 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (6 : ℝ) * b^2 * (c - a)^2 + (8 : ℝ) * b^1 * (a - b)^3 + (14 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (14 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (4 : ℝ) * b^1 * (c - a)^3 + (2 : ℝ) * (a - b)^4 + (4 : ℝ) * (a - b)^3 * (c - a)^1 + (6 : ℝ) * (a - b)^2 * (c - a)^2 + (4 : ℝ) * (a - b)^1 * (c - a)^3 + (1 : ℝ) * (c - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (a^4 - 2*a^2*b*c + 2*a*b^2*c + 2*a*b*c^2 + b^4 - 2*b^2*c^2 + c^4) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * b^4 + (8 : ℝ) * b^3 * (c - b)^1 + (4 : ℝ) * b^3 * (a - c)^1 + (12 : ℝ) * b^2 * (c - b)^2 + (10 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^2 * (a - c)^2 + (8 : ℝ) * b^1 * (c - b)^3 + (10 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (10 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (4 : ℝ) * b^1 * (a - c)^3 + (2 : ℝ) * (c - b)^4 + (4 : ℝ) * (c - b)^3 * (a - c)^1 + (6 : ℝ) * (c - b)^2 * (a - c)^2 + (4 : ℝ) * (c - b)^1 * (a - c)^3 + (1 : ℝ) * (a - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4 - 2*a^2*b*c + 2*a*b^2*c + 2*a*b*c^2 + b^4 - 2*b^2*c^2 + c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), a^4 + b^4 + c^4 ≥ 2 * b * c * (a - b) * (a - c)) := @solution
#print axioms solution
