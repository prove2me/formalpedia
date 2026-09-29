-- Prove2me | solution 1 for WorkbookSource.base_4678
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:18.552737+00:00
-- url     : https://prove2.me/submissions/715a48ec-a573-4b79-b8a5-177e98a9e04e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a + (27 * a * b * c) / (2 * (a + b + c)^2)) ≥ (3 / 2) * (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + a^4*b*c + 4*a^4*c^2 + 2*a^3*b^3 - 7*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 4*a^2*b^4 - 5*a^2*b^3*c + 9*a^2*b^2*c^2 - 7*a^2*b*c^3 + 2*a*b^5 + a*b^4*c - 7*a*b^3*c^2 - 5*a*b^2*c^3 + a*b*c^4 + 2*b^3*c^3 + 4*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^4 * (b - a)^2 + (27 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^4 * (c - b)^2 + (76 : ℝ) * a^3 * (b - a)^3 + (141 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (129 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^3 * (c - b)^3 + (81 : ℝ) * a^2 * (b - a)^4 + (216 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (240 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (105 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (15 : ℝ) * a^2 * (c - b)^4 + (40 : ℝ) * a^1 * (b - a)^5 + (136 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (184 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (113 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (29 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (8 : ℝ) * (b - a)^6 + (32 : ℝ) * (b - a)^5 * (c - b)^1 + (50 : ℝ) * (b - a)^4 * (c - b)^2 + (38 : ℝ) * (b - a)^3 * (c - b)^3 + (14 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + a^4*b*c + 4*a^4*c^2 + 2*a^3*b^3 - 7*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 4*a^2*b^4 - 5*a^2*b^3*c + 9*a^2*b^2*c^2 - 7*a^2*b*c^3 + 2*a*b^5 + a*b^4*c - 7*a*b^3*c^2 - 5*a*b^2*c^3 + a*b*c^4 + 2*b^3*c^3 + 4*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^4 * (c - a)^2 + (27 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (27 : ℝ) * a^4 * (b - c)^2 + (76 : ℝ) * a^3 * (c - a)^3 + (87 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (75 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (32 : ℝ) * a^3 * (b - c)^3 + (81 : ℝ) * a^2 * (c - a)^4 + (108 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (78 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (51 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (15 : ℝ) * a^2 * (b - c)^4 + (40 : ℝ) * a^1 * (c - a)^5 + (64 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (40 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (23 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (11 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (8 : ℝ) * (c - a)^6 + (16 : ℝ) * (c - a)^5 * (b - c)^1 + (10 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + a^4*b*c + 4*a^4*c^2 + 2*a^3*b^3 - 7*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 4*a^2*b^4 - 5*a^2*b^3*c + 9*a^2*b^2*c^2 - 7*a^2*b*c^3 + 2*a*b^5 + a*b^4*c - 7*a*b^3*c^2 - 5*a*b^2*c^3 + a*b*c^4 + 2*b^3*c^3 + 4*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + a^4*b*c + 4*a^4*c^2 + 2*a^3*b^3 - 7*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 4*a^2*b^4 - 5*a^2*b^3*c + 9*a^2*b^2*c^2 - 7*a^2*b*c^3 + 2*a*b^5 + a*b^4*c - 7*a*b^3*c^2 - 5*a*b^2*c^3 + a*b*c^4 + 2*b^3*c^3 + 4*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b + b^2 / c + c^2 / a + (27 * a * b * c) / (2 * (a + b + c)^2)) ≥ (3 / 2) * (a + b + c)) := @solution
#print axioms solution
