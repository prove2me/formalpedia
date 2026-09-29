-- Prove2me | solution 1 for WorkbookSource.base_9399
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:18.223604+00:00
-- url     : https://prove2.me/submissions/e0ab4e4a-5598-4618-8f49-955c97eaddc4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 / (c * (a + b + 2 * c)) + (b + c) ^ 2 / (a * (b + c + 2 * a)) + (c + a) ^ 2 / (b * (c + a + 2 * b)) + 1 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 9*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 + 9*a^5*c^3 + 14*a^4*b^4 + 4*a^4*b^3*c - 22*a^4*b^2*c^2 + 4*a^4*b*c^3 + 14*a^4*c^4 + 9*a^3*b^5 + 4*a^3*b^4*c + 4*a^3*b*c^4 + 9*a^3*c^5 + 2*a^2*b^6 - 9*a^2*b^5*c - 22*a^2*b^4*c^2 - 22*a^2*b^2*c^4 - 9*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c - 9*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 9*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 9*b^5*c^3 + 14*b^4*c^4 + 9*b^3*c^5 + 2*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (104 : ℝ) * a^6 * (b - a)^2 + (104 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (104 : ℝ) * a^6 * (c - b)^2 + (542 : ℝ) * a^5 * (b - a)^3 + (813 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (435 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (82 : ℝ) * a^5 * (c - b)^3 + (1164 : ℝ) * a^4 * (b - a)^4 + (2328 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1397 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (233 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (14 : ℝ) * a^4 * (c - b)^4 + (1316 : ℝ) * a^3 * (b - a)^5 + (3290 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2688 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (742 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (28 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (824 : ℝ) * a^2 * (b - a)^6 + (2472 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (2666 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1212 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (194 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (270 : ℝ) * a^1 * (b - a)^7 + (945 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1275 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (825 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (255 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (30 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (36 : ℝ) * (b - a)^8 + (144 : ℝ) * (b - a)^7 * (c - b)^1 + (233 : ℝ) * (b - a)^6 * (c - b)^2 + (195 : ℝ) * (b - a)^5 * (c - b)^3 + (89 : ℝ) * (b - a)^4 * (c - b)^4 + (21 : ℝ) * (b - a)^3 * (c - b)^5 + (2 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 9*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 + 9*a^5*c^3 + 14*a^4*b^4 + 4*a^4*b^3*c - 22*a^4*b^2*c^2 + 4*a^4*b*c^3 + 14*a^4*c^4 + 9*a^3*b^5 + 4*a^3*b^4*c + 4*a^3*b*c^4 + 9*a^3*c^5 + 2*a^2*b^6 - 9*a^2*b^5*c - 22*a^2*b^4*c^2 - 22*a^2*b^2*c^4 - 9*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c - 9*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 9*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 9*b^5*c^3 + 14*b^4*c^4 + 9*b^3*c^5 + 2*b^2*c^6) := by
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
  have hn : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 9*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 + 9*a^5*c^3 + 14*a^4*b^4 + 4*a^4*b^3*c - 22*a^4*b^2*c^2 + 4*a^4*b*c^3 + 14*a^4*c^4 + 9*a^3*b^5 + 4*a^3*b^4*c + 4*a^3*b*c^4 + 9*a^3*c^5 + 2*a^2*b^6 - 9*a^2*b^5*c - 22*a^2*b^4*c^2 - 22*a^2*b^2*c^4 - 9*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c - 9*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 9*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 9*b^5*c^3 + 14*b^4*c^4 + 9*b^3*c^5 + 2*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 2 / (c * (a + b + 2 * c)) + (b + c) ^ 2 / (a * (b + c + 2 * a)) + (c + a) ^ 2 / (b * (c + a + 2 * b)) + 1 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)) := @solution
#print axioms solution
