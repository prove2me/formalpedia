-- Prove2me | solution 1 for WorkbookSource.base_39011
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:56.461095+00:00
-- url     : https://prove2.me/submissions/2f23d5ea-2e46-4559-ac4f-3672ef92be9e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / a + (c + a) / b ≥ 18 / 5 + 18 / 5 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 + 2 / 5 * (a + b + c) ^ 2 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^5*b^2 + 8*a^5*b*c + 5*a^5*c^2 + 15*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 15*a^4*c^3 + 15*a^3*b^4 + 12*a^3*b^3*c - 52*a^3*b^2*c^2 + 12*a^3*b*c^3 + 15*a^3*c^4 + 5*a^2*b^5 - 4*a^2*b^4*c - 52*a^2*b^3*c^2 - 52*a^2*b^2*c^3 - 4*a^2*b*c^4 + 5*a^2*c^5 + 8*a*b^5*c - 4*a*b^4*c^2 + 12*a*b^3*c^3 - 4*a*b^2*c^4 + 8*a*b*c^5 + 5*b^5*c^2 + 15*b^4*c^3 + 15*b^3*c^4 + 5*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (216 : ℝ) * a^5 * (b - a)^2 + (216 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (216 : ℝ) * a^5 * (c - b)^2 + (810 : ℝ) * a^4 * (b - a)^3 + (1215 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (945 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (270 : ℝ) * a^4 * (c - b)^3 + (1192 : ℝ) * a^3 * (b - a)^4 + (2384 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (1956 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (764 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (112 : ℝ) * a^3 * (c - b)^4 + (858 : ℝ) * a^2 * (b - a)^5 + (2145 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (2070 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (960 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (213 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^2 * (c - b)^5 + (300 : ℝ) * a^1 * (b - a)^6 + (900 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1038 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (576 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (156 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (40 : ℝ) * (b - a)^7 + (140 : ℝ) * (b - a)^6 * (c - b)^1 + (190 : ℝ) * (b - a)^5 * (c - b)^2 + (125 : ℝ) * (b - a)^4 * (c - b)^3 + (40 : ℝ) * (b - a)^3 * (c - b)^4 + (5 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^5*b^2 + 8*a^5*b*c + 5*a^5*c^2 + 15*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 15*a^4*c^3 + 15*a^3*b^4 + 12*a^3*b^3*c - 52*a^3*b^2*c^2 + 12*a^3*b*c^3 + 15*a^3*c^4 + 5*a^2*b^5 - 4*a^2*b^4*c - 52*a^2*b^3*c^2 - 52*a^2*b^2*c^3 - 4*a^2*b*c^4 + 5*a^2*c^5 + 8*a*b^5*c - 4*a*b^4*c^2 + 12*a*b^3*c^3 - 4*a*b^2*c^4 + 8*a*b*c^5 + 5*b^5*c^2 + 15*b^4*c^3 + 15*b^3*c^4 + 5*b^2*c^5) := by
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
  have hn : 0 ≤ (5*a^5*b^2 + 8*a^5*b*c + 5*a^5*c^2 + 15*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 15*a^4*c^3 + 15*a^3*b^4 + 12*a^3*b^3*c - 52*a^3*b^2*c^2 + 12*a^3*b*c^3 + 15*a^3*c^4 + 5*a^2*b^5 - 4*a^2*b^4*c - 52*a^2*b^3*c^2 - 52*a^2*b^2*c^3 - 4*a^2*b*c^4 + 5*a^2*c^5 + 8*a*b^5*c - 4*a*b^4*c^2 + 12*a*b^3*c^3 - 4*a*b^2*c^4 + 8*a*b*c^5 + 5*b^5*c^2 + 15*b^4*c^3 + 15*b^3*c^4 + 5*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / c + (b + c) / a + (c + a) / b ≥ 18 / 5 + 18 / 5 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 + 2 / 5 * (a + b + c) ^ 2 / (a * b + b * c + c * a)) := @solution
#print axioms solution
