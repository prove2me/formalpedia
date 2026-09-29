-- Prove2me | solution 1 for WorkbookSource.plus_79615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:26.470829+00:00
-- url     : https://prove2.me/submissions/3c9823bd-35c5-4145-a104-b0f5613fbd56

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 / (2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)) + 1 ≥ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 7*a^4*b^2 - 3*a^4*b*c - 7*a^4*c^2 + 8*a^3*b^3 + 5*a^3*b^2*c + 5*a^3*b*c^2 + 8*a^3*c^3 - 7*a^2*b^4 + 5*a^2*b^3*c - 18*a^2*b^2*c^2 + 5*a^2*b*c^3 - 7*a^2*c^4 + 2*a*b^5 - 3*a*b^4*c + 5*a*b^3*c^2 + 5*a*b^2*c^3 - 3*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - 7*b^4*c^2 + 8*b^3*c^3 - 7*b^2*c^4 + 2*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (18 : ℝ) * a^3 * (b - a)^3 + (27 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^3 * (c - b)^3 + (18 : ℝ) * a^2 * (b - a)^4 + (36 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (81 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (63 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^2 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^5 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (62 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (73 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (43 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^1 * (c - b)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^2 + (20 : ℝ) * (b - a)^3 * (c - b)^3 + (18 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 7*a^4*b^2 - 3*a^4*b*c - 7*a^4*c^2 + 8*a^3*b^3 + 5*a^3*b^2*c + 5*a^3*b*c^2 + 8*a^3*c^3 - 7*a^2*b^4 + 5*a^2*b^3*c - 18*a^2*b^2*c^2 + 5*a^2*b*c^3 - 7*a^2*c^4 + 2*a*b^5 - 3*a*b^4*c + 5*a*b^3*c^2 + 5*a*b^2*c^3 - 3*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - 7*b^4*c^2 + 8*b^3*c^3 - 7*b^2*c^4 + 2*b*c^5 + c^6) := by
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
  have hn : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 7*a^4*b^2 - 3*a^4*b*c - 7*a^4*c^2 + 8*a^3*b^3 + 5*a^3*b^2*c + 5*a^3*b*c^2 + 8*a^3*c^3 - 7*a^2*b^4 + 5*a^2*b^3*c - 18*a^2*b^2*c^2 + 5*a^2*b*c^3 - 7*a^2*c^4 + 2*a*b^5 - 3*a*b^4*c + 5*a*b^3*c^2 + 5*a*b^2*c^3 - 3*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - 7*b^4*c^2 + 8*b^3*c^3 - 7*b^2*c^4 + 2*b*c^5 + c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2)^2 / (2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)) + 1 ≥ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2) := @solution
#print axioms solution
