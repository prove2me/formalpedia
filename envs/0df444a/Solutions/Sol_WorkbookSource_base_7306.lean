-- Prove2me | solution 1 for WorkbookSource.base_7306
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:08.091081+00:00
-- url     : https://prove2.me/submissions/0851f87e-30f7-4a97-9336-d6b53d94ad01

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 16 * b * c) / (b^2 + b * c + c^2) + (b^2 + 16 * c * a) / (c^2 + c * a + a^2) + (c^2 + 16 * a * b) / (a^2 + a * b + b^2) ≥ 20 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 17*a^4*b^2 + 31*a^4*b*c - 17*a^4*c^2 + 28*a^3*b^3 + 107*a^3*b^2*c + 107*a^3*b*c^2 + 28*a^3*c^3 - 17*a^2*b^4 + 107*a^2*b^3*c + 93*a^2*b^2*c^2 + 107*a^2*b*c^3 - 17*a^2*c^4 + 3*a*b^5 + 31*a*b^4*c + 107*a*b^3*c^2 + 107*a*b^2*c^3 + 31*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 17*b^4*c^2 + 28*b^3*c^3 - 17*b^2*c^4 + 3*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (837 : ℝ) * a^6 + (3348 : ℝ) * a^5 * (b - a)^1 + (1674 : ℝ) * a^5 * (c - b)^1 + (5355 : ℝ) * a^4 * (b - a)^2 + (5355 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1170 : ℝ) * a^4 * (c - b)^2 + (4302 : ℝ) * a^3 * (b - a)^3 + (6453 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2907 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (378 : ℝ) * a^3 * (c - b)^3 + (1773 : ℝ) * a^2 * (b - a)^4 + (3546 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2484 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (711 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (72 : ℝ) * a^2 * (c - b)^4 + (318 : ℝ) * a^1 * (b - a)^5 + (795 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (804 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (411 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (132 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^1 * (c - b)^5 + (6 : ℝ) * (b - a)^6 + (18 : ℝ) * (b - a)^5 * (c - b)^1 + (40 : ℝ) * (b - a)^4 * (c - b)^2 + (50 : ℝ) * (b - a)^3 * (c - b)^3 + (43 : ℝ) * (b - a)^2 * (c - b)^4 + (21 : ℝ) * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 17*a^4*b^2 + 31*a^4*b*c - 17*a^4*c^2 + 28*a^3*b^3 + 107*a^3*b^2*c + 107*a^3*b*c^2 + 28*a^3*c^3 - 17*a^2*b^4 + 107*a^2*b^3*c + 93*a^2*b^2*c^2 + 107*a^2*b*c^3 - 17*a^2*c^4 + 3*a*b^5 + 31*a*b^4*c + 107*a*b^3*c^2 + 107*a*b^2*c^3 + 31*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 17*b^4*c^2 + 28*b^3*c^3 - 17*b^2*c^4 + 3*b*c^5 + 3*c^6) := by
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
  have hn : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 17*a^4*b^2 + 31*a^4*b*c - 17*a^4*c^2 + 28*a^3*b^3 + 107*a^3*b^2*c + 107*a^3*b*c^2 + 28*a^3*c^3 - 17*a^2*b^4 + 107*a^2*b^3*c + 93*a^2*b^2*c^2 + 107*a^2*b*c^3 - 17*a^2*c^4 + 3*a*b^5 + 31*a*b^4*c + 107*a*b^3*c^2 + 107*a*b^2*c^3 + 31*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 17*b^4*c^2 + 28*b^3*c^3 - 17*b^2*c^4 + 3*b*c^5 + 3*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 16 * b * c) / (b^2 + b * c + c^2) + (b^2 + 16 * c * a) / (c^2 + c * a + a^2) + (c^2 + 16 * a * b) / (a^2 + a * b + b^2) ≥ 20 / 3) := @solution
#print axioms solution
