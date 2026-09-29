-- Prove2me | solution 1 for WorkbookSource.plus_67957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:53.309077+00:00
-- url     : https://prove2.me/submissions/fac265ce-afb8-4ede-a7fe-a38670f64113

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c) ^ 2 / ((a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)) ≤ (3 * (a * b + b * c + a * c) * (a + b + c)) / (8 * (a + b + c) ^ 3)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5*b^2*c + 3*a^5*b*c^2 + 3*a^4*b^4 + 3*a^4*b^3*c - 5*a^4*b^2*c^2 + 3*a^4*b*c^3 + 3*a^4*c^4 + 3*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 3*a^3*b*c^4 + 3*a^2*b^5*c - 5*a^2*b^4*c^2 - 10*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 3*a^2*b*c^5 + 3*a*b^5*c^2 + 3*a*b^4*c^3 + 3*a*b^3*c^4 + 3*a*b^2*c^5 + 3*b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (46 : ℝ) * a^6 * (b - a)^2 + (46 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (46 : ℝ) * a^6 * (c - b)^2 + (202 : ℝ) * a^5 * (b - a)^3 + (303 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (249 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (74 : ℝ) * a^5 * (c - b)^3 + (357 : ℝ) * a^4 * (b - a)^4 + (714 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (616 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (259 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (37 : ℝ) * a^4 * (c - b)^4 + (322 : ℝ) * a^3 * (b - a)^5 + (805 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (798 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (392 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (89 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (154 : ℝ) * a^2 * (b - a)^6 + (462 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (535 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (300 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (82 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (36 : ℝ) * a^1 * (b - a)^7 + (126 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (168 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (105 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (30 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * (b - a)^8 + (12 : ℝ) * (b - a)^7 * (c - b)^1 + (18 : ℝ) * (b - a)^6 * (c - b)^2 + (12 : ℝ) * (b - a)^5 * (c - b)^3 + (3 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5*b^2*c + 3*a^5*b*c^2 + 3*a^4*b^4 + 3*a^4*b^3*c - 5*a^4*b^2*c^2 + 3*a^4*b*c^3 + 3*a^4*c^4 + 3*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 3*a^3*b*c^4 + 3*a^2*b^5*c - 5*a^2*b^4*c^2 - 10*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 3*a^2*b*c^5 + 3*a*b^5*c^2 + 3*a*b^4*c^3 + 3*a*b^3*c^4 + 3*a*b^2*c^5 + 3*b^4*c^4) := by
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
  have hn : 0 ≤ (3*a^5*b^2*c + 3*a^5*b*c^2 + 3*a^4*b^4 + 3*a^4*b^3*c - 5*a^4*b^2*c^2 + 3*a^4*b*c^3 + 3*a^4*c^4 + 3*a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 3*a^3*b*c^4 + 3*a^2*b^5*c - 5*a^2*b^4*c^2 - 10*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 3*a^2*b*c^5 + 3*a*b^5*c^2 + 3*a*b^4*c^3 + 3*a*b^3*c^4 + 3*a*b^2*c^5 + 3*b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * c) ^ 2 / ((a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)) ≤ (3 * (a * b + b * c + a * c) * (a + b + c)) / (8 * (a + b + c) ^ 3)) := @solution
#print axioms solution
