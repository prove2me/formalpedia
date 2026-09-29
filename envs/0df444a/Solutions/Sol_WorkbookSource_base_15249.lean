-- Prove2me | solution 1 for WorkbookSource.base_15249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:01.288914+00:00
-- url     : https://prove2.me/submissions/065e9e73-3334-4727-a871-7dbbe53243a9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (4 * a + b + c) + 1 / (4 * b + c + a) + 1 / (4 * c + a + b) + 3 / (a + b + c)) ≤ (1 / (a + b) + 1 / (b + c) + 1 / (c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 16*a^5*b + 16*a^5*c + a^4*b^2 + 42*a^4*b*c + a^4*c^2 - 22*a^3*b^3 - 26*a^3*b^2*c - 26*a^3*b*c^2 - 22*a^3*c^3 + a^2*b^4 - 26*a^2*b^3*c - 18*a^2*b^2*c^2 - 26*a^2*b*c^3 + a^2*c^4 + 16*a*b^5 + 42*a*b^4*c - 26*a*b^3*c^2 - 26*a*b^2*c^3 + 42*a*b*c^4 + 16*a*c^5 + 4*b^6 + 16*b^5*c + b^4*c^2 - 22*b^3*c^3 + b^2*c^4 + 16*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (288 : ℝ) * a^4 * (b - a)^2 + (288 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (288 : ℝ) * a^4 * (c - b)^2 + (672 : ℝ) * a^3 * (b - a)^3 + (1008 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1296 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (480 : ℝ) * a^3 * (c - b)^3 + (552 : ℝ) * a^2 * (b - a)^4 + (1104 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1800 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1248 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (264 : ℝ) * a^2 * (c - b)^4 + (184 : ℝ) * a^1 * (b - a)^5 + (460 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (952 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (968 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (404 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (56 : ℝ) * a^1 * (c - b)^5 + (20 : ℝ) * (b - a)^6 + (60 : ℝ) * (b - a)^5 * (c - b)^1 + (161 : ℝ) * (b - a)^4 * (c - b)^2 + (222 : ℝ) * (b - a)^3 * (c - b)^3 + (141 : ℝ) * (b - a)^2 * (c - b)^4 + (40 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 16*a^5*b + 16*a^5*c + a^4*b^2 + 42*a^4*b*c + a^4*c^2 - 22*a^3*b^3 - 26*a^3*b^2*c - 26*a^3*b*c^2 - 22*a^3*c^3 + a^2*b^4 - 26*a^2*b^3*c - 18*a^2*b^2*c^2 - 26*a^2*b*c^3 + a^2*c^4 + 16*a*b^5 + 42*a*b^4*c - 26*a*b^3*c^2 - 26*a*b^2*c^3 + 42*a*b*c^4 + 16*a*c^5 + 4*b^6 + 16*b^5*c + b^4*c^2 - 22*b^3*c^3 + b^2*c^4 + 16*b*c^5 + 4*c^6) := by
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
  have hn : 0 ≤ (4*a^6 + 16*a^5*b + 16*a^5*c + a^4*b^2 + 42*a^4*b*c + a^4*c^2 - 22*a^3*b^3 - 26*a^3*b^2*c - 26*a^3*b*c^2 - 22*a^3*c^3 + a^2*b^4 - 26*a^2*b^3*c - 18*a^2*b^2*c^2 - 26*a^2*b*c^3 + a^2*c^4 + 16*a*b^5 + 42*a*b^4*c - 26*a*b^3*c^2 - 26*a*b^2*c^3 + 42*a*b*c^4 + 16*a*c^5 + 4*b^6 + 16*b^5*c + b^4*c^2 - 22*b^3*c^3 + b^2*c^4 + 16*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (4 * a + b + c) + 1 / (4 * b + c + a) + 1 / (4 * c + a + b) + 3 / (a + b + c)) ≤ (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) := @solution
#print axioms solution
