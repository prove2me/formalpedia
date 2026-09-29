-- Prove2me | solution 1 for WorkbookSource.plus_71510
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:22.247631+00:00
-- url     : https://prove2.me/submissions/dac36b7e-aae7-4b68-b1ef-dfa8d0c188b0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 + (c + a + 2 * b) / (b + 2 * c) ^ 2 ≥ 4 / (a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 28*a^5*b + 12*a^5*c + 65*a^4*b^2 + 44*a^4*b*c - 15*a^4*c^2 + 34*a^3*b^3 - 25*a^3*b^2*c - 89*a^3*b*c^2 + 34*a^3*c^3 - 15*a^2*b^4 - 89*a^2*b^3*c - 174*a^2*b^2*c^2 - 25*a^2*b*c^3 + 65*a^2*c^4 + 12*a*b^5 + 44*a*b^4*c - 25*a*b^3*c^2 - 89*a*b^2*c^3 + 44*a*b*c^4 + 28*a*c^5 + 4*b^6 + 28*b^5*c + 65*b^4*c^2 + 34*b^3*c^3 - 15*b^2*c^4 + 12*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (648 : ℝ) * a^4 * (b - a)^2 + (648 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (648 : ℝ) * a^4 * (c - b)^2 + (1782 : ℝ) * a^3 * (b - a)^3 + (2241 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2079 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (810 : ℝ) * a^3 * (c - b)^3 + (1812 : ℝ) * a^2 * (b - a)^4 + (2760 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2439 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1491 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (354 : ℝ) * a^2 * (c - b)^4 + (806 : ℝ) * a^1 * (b - a)^5 + (1463 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1280 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (889 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (394 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (64 : ℝ) * a^1 * (c - b)^5 + (132 : ℝ) * (b - a)^6 + (284 : ℝ) * (b - a)^5 * (c - b)^1 + (257 : ℝ) * (b - a)^4 * (c - b)^2 + (174 : ℝ) * (b - a)^3 * (c - b)^3 + (105 : ℝ) * (b - a)^2 * (c - b)^4 + (36 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6 + 28*a^5*b + 12*a^5*c + 65*a^4*b^2 + 44*a^4*b*c - 15*a^4*c^2 + 34*a^3*b^3 - 25*a^3*b^2*c - 89*a^3*b*c^2 + 34*a^3*c^3 - 15*a^2*b^4 - 89*a^2*b^3*c - 174*a^2*b^2*c^2 - 25*a^2*b*c^3 + 65*a^2*c^4 + 12*a*b^5 + 44*a*b^4*c - 25*a*b^3*c^2 - 89*a*b^2*c^3 + 44*a*b*c^4 + 28*a*c^5 + 4*b^6 + 28*b^5*c + 65*b^4*c^2 + 34*b^3*c^3 - 15*b^2*c^4 + 12*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (648 : ℝ) * a^4 * (c - a)^2 + (648 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (648 : ℝ) * a^4 * (b - c)^2 + (1782 : ℝ) * a^3 * (c - a)^3 + (3105 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (2943 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (810 : ℝ) * a^3 * (b - c)^3 + (1812 : ℝ) * a^2 * (c - a)^4 + (4488 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (5031 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (2355 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (354 : ℝ) * a^2 * (b - c)^4 + (806 : ℝ) * a^1 * (c - a)^5 + (2567 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (3488 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (2233 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (634 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (64 : ℝ) * a^1 * (b - c)^5 + (132 : ℝ) * (c - a)^6 + (508 : ℝ) * (c - a)^5 * (b - c)^1 + (817 : ℝ) * (c - a)^4 * (b - c)^2 + (654 : ℝ) * (c - a)^3 * (b - c)^3 + (265 : ℝ) * (c - a)^2 * (b - c)^4 + (52 : ℝ) * (c - a)^1 * (b - c)^5 + (4 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 28*a^5*b + 12*a^5*c + 65*a^4*b^2 + 44*a^4*b*c - 15*a^4*c^2 + 34*a^3*b^3 - 25*a^3*b^2*c - 89*a^3*b*c^2 + 34*a^3*c^3 - 15*a^2*b^4 - 89*a^2*b^3*c - 174*a^2*b^2*c^2 - 25*a^2*b*c^3 + 65*a^2*c^4 + 12*a*b^5 + 44*a*b^4*c - 25*a*b^3*c^2 - 89*a*b^2*c^3 + 44*a*b*c^4 + 28*a*c^5 + 4*b^6 + 28*b^5*c + 65*b^4*c^2 + 34*b^3*c^3 - 15*b^2*c^4 + 12*b*c^5 + 4*c^6) := by
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
  have hn : 0 ≤ (4*a^6 + 28*a^5*b + 12*a^5*c + 65*a^4*b^2 + 44*a^4*b*c - 15*a^4*c^2 + 34*a^3*b^3 - 25*a^3*b^2*c - 89*a^3*b*c^2 + 34*a^3*c^3 - 15*a^2*b^4 - 89*a^2*b^3*c - 174*a^2*b^2*c^2 - 25*a^2*b*c^3 + 65*a^2*c^4 + 12*a*b^5 + 44*a*b^4*c - 25*a*b^3*c^2 - 89*a*b^2*c^3 + 44*a*b*c^4 + 28*a*c^5 + 4*b^6 + 28*b^5*c + 65*b^4*c^2 + 34*b^3*c^3 - 15*b^2*c^4 + 12*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 + (c + a + 2 * b) / (b + 2 * c) ^ 2 ≥ 4 / (a + b + c)) := @solution
#print axioms solution
