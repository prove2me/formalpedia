-- Prove2me | solution 1 for WorkbookSource.base_48460
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:27:02.794099+00:00
-- url     : https://prove2.me/submissions/3e6335b5-19d5-4169-b983-e9c87bd1f7b2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 1 / (2 * (a * b + a * c + b * c)) + 4 / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7*b + 2*a^7*c - a^6*b^2 + 2*a^6*b*c - a^6*c^2 - 2*a^4*b^4 - 4*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - a^2*b^6 - 4*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 - a^2*c^6 + 2*a*b^7 + 2*a*b^6*c + 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c - b^6*c^2 - 2*b^4*c^4 - b^2*c^6 + 2*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^6 * (b - a)^2 + (40 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^6 * (c - b)^2 + (128 : ℝ) * a^5 * (b - a)^3 + (192 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (288 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (112 : ℝ) * a^5 * (c - b)^3 + (172 : ℝ) * a^4 * (b - a)^4 + (344 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (716 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (544 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (132 : ℝ) * a^4 * (c - b)^4 + (124 : ℝ) * a^3 * (b - a)^5 + (310 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (860 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (980 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (474 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (84 : ℝ) * a^3 * (c - b)^5 + (48 : ℝ) * a^2 * (b - a)^6 + (144 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (533 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (826 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (599 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (210 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (28 : ℝ) * a^2 * (c - b)^6 + (8 : ℝ) * a^1 * (b - a)^7 + (28 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (156 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (320 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (312 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (162 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (42 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * a^1 * (c - b)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (42 : ℝ) * (b - a)^5 * (c - b)^3 + (53 : ℝ) * (b - a)^4 * (c - b)^4 + (36 : ℝ) * (b - a)^3 * (c - b)^5 + (13 : ℝ) * (b - a)^2 * (c - b)^6 + (2 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7*b + 2*a^7*c - a^6*b^2 + 2*a^6*b*c - a^6*c^2 - 2*a^4*b^4 - 4*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - a^2*b^6 - 4*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 - a^2*c^6 + 2*a*b^7 + 2*a*b^6*c + 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c - b^6*c^2 - 2*b^4*c^4 - b^2*c^6 + 2*b*c^7) := by
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
  have hn : 0 ≤ (2*a^7*b + 2*a^7*c - a^6*b^2 + 2*a^6*b*c - a^6*c^2 - 2*a^4*b^4 - 4*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - a^2*b^6 - 4*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 - a^2*c^6 + 2*a*b^7 + 2*a*b^6*c + 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c - b^6*c^2 - 2*b^4*c^4 - b^2*c^6 + 2*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 1 / (2 * (a * b + a * c + b * c)) + 4 / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
