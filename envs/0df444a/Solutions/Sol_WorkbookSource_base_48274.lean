-- Prove2me | solution 1 for WorkbookSource.base_48274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:21:25.20085+00:00
-- url     : https://prove2.me/submissions/6eee6acf-f2e6-46c2-bd18-7b52b3a6dc18

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + b + c) + 1 / (a + 2 * b + c) + 1 / (a + b + 2 * c)) ≤ (27 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a + b + c) ^ 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (34*a^5 + 85*a^4*b + 85*a^4*c + 31*a^3*b^2 + 4*a^3*b*c + 31*a^3*c^2 + 31*a^2*b^3 - 270*a^2*b^2*c - 270*a^2*b*c^2 + 31*a^2*c^3 + 85*a*b^4 + 4*a*b^3*c - 270*a*b^2*c^2 + 4*a*b*c^3 + 85*a*c^4 + 34*b^5 + 85*b^4*c + 31*b^3*c^2 + 31*b^2*c^3 + 85*b*c^4 + 34*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1080 : ℝ) * a^3 * (b - a)^2 + (1080 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1080 : ℝ) * a^3 * (c - b)^2 + (2154 : ℝ) * a^2 * (b - a)^3 + (3231 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (3249 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (1086 : ℝ) * a^2 * (c - b)^3 + (1408 : ℝ) * a^1 * (b - a)^4 + (2816 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (3174 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (1766 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (340 : ℝ) * a^1 * (c - b)^4 + (300 : ℝ) * (b - a)^5 + (750 : ℝ) * (b - a)^4 * (c - b)^1 + (974 : ℝ) * (b - a)^3 * (c - b)^2 + (711 : ℝ) * (b - a)^2 * (c - b)^3 + (255 : ℝ) * (b - a)^1 * (c - b)^4 + (34 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (34*a^5 + 85*a^4*b + 85*a^4*c + 31*a^3*b^2 + 4*a^3*b*c + 31*a^3*c^2 + 31*a^2*b^3 - 270*a^2*b^2*c - 270*a^2*b*c^2 + 31*a^2*c^3 + 85*a*b^4 + 4*a*b^3*c - 270*a*b^2*c^2 + 4*a*b*c^3 + 85*a*c^4 + 34*b^5 + 85*b^4*c + 31*b^3*c^2 + 31*b^2*c^3 + 85*b*c^4 + 34*c^5) := by
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
  have hn : 0 ≤ (34*a^5 + 85*a^4*b + 85*a^4*c + 31*a^3*b^2 + 4*a^3*b*c + 31*a^3*c^2 + 31*a^2*b^3 - 270*a^2*b^2*c - 270*a^2*b*c^2 + 31*a^2*c^3 + 85*a*b^4 + 4*a*b^3*c - 270*a*b^2*c^2 + 4*a*b*c^3 + 85*a*c^4 + 34*b^5 + 85*b^4*c + 31*b^3*c^2 + 31*b^2*c^3 + 85*b*c^4 + 34*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a + b + c) + 1 / (a + 2 * b + c) + 1 / (a + b + 2 * c)) ≤ (27 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a + b + c) ^ 3)) := @solution
#print axioms solution
