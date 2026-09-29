-- Prove2me | solution 1 for WorkbookSource.base_20388
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:46:40.773716+00:00
-- url     : https://prove2.me/submissions/a92fe3a5-9175-4574-b6d8-a84400d7e008

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a + b) * (5 * a - b) / (b + c) + (3 * b + c) * (5 * b - c) / (c + a) + (3 * c + a) * (5 * c - a) / (a + b) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3) / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (15*a^6 - 8*a^5*b - 10*a^5*c - 8*a^4*b^2 - 30*a^4*b*c - 8*a^4*c^2 + 30*a^3*b^3 + 8*a^3*b^2*c + 10*a^3*b*c^2 + 30*a^3*c^3 - 8*a^2*b^4 + 10*a^2*b^3*c + 3*a^2*b^2*c^2 + 8*a^2*b*c^3 - 8*a^2*c^4 - 10*a*b^5 - 30*a*b^4*c + 8*a*b^3*c^2 + 10*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 15*b^6 - 8*b^5*c - 8*b^4*c^2 + 30*b^3*c^3 - 8*b^2*c^4 - 10*b*c^5 + 15*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (18 : ℝ) * a^3 * (b - a)^3 + (18 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (28 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^3 * (c - b)^3 + (95 : ℝ) * a^2 * (b - a)^4 + (172 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (267 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (190 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (89 : ℝ) * a^2 * (c - b)^4 + (96 : ℝ) * a^1 * (b - a)^5 + (226 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (414 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (404 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (264 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (72 : ℝ) * a^1 * (c - b)^5 + (26 : ℝ) * (b - a)^6 + (74 : ℝ) * (b - a)^5 * (c - b)^1 + (159 : ℝ) * (b - a)^4 * (c - b)^2 + (198 : ℝ) * (b - a)^3 * (c - b)^3 + (167 : ℝ) * (b - a)^2 * (c - b)^4 + (80 : ℝ) * (b - a)^1 * (c - b)^5 + (15 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (15*a^6 - 8*a^5*b - 10*a^5*c - 8*a^4*b^2 - 30*a^4*b*c - 8*a^4*c^2 + 30*a^3*b^3 + 8*a^3*b^2*c + 10*a^3*b*c^2 + 30*a^3*c^3 - 8*a^2*b^4 + 10*a^2*b^3*c + 3*a^2*b^2*c^2 + 8*a^2*b*c^3 - 8*a^2*c^4 - 10*a*b^5 - 30*a*b^4*c + 8*a*b^3*c^2 + 10*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 15*b^6 - 8*b^5*c - 8*b^4*c^2 + 30*b^3*c^3 - 8*b^2*c^4 - 10*b*c^5 + 15*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (c - a)^2 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^4 * (b - c)^2 + (18 : ℝ) * a^3 * (c - a)^3 + (36 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (46 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (14 : ℝ) * a^3 * (b - c)^3 + (95 : ℝ) * a^2 * (c - a)^4 + (208 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (321 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (208 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (89 : ℝ) * a^2 * (b - c)^4 + (96 : ℝ) * a^1 * (c - a)^5 + (254 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (470 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (442 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (274 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (72 : ℝ) * a^1 * (b - c)^5 + (26 : ℝ) * (c - a)^6 + (82 : ℝ) * (c - a)^5 * (b - c)^1 + (179 : ℝ) * (c - a)^4 * (b - c)^2 + (218 : ℝ) * (c - a)^3 * (b - c)^3 + (177 : ℝ) * (c - a)^2 * (b - c)^4 + (82 : ℝ) * (c - a)^1 * (b - c)^5 + (15 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (15*a^6 - 8*a^5*b - 10*a^5*c - 8*a^4*b^2 - 30*a^4*b*c - 8*a^4*c^2 + 30*a^3*b^3 + 8*a^3*b^2*c + 10*a^3*b*c^2 + 30*a^3*c^3 - 8*a^2*b^4 + 10*a^2*b^3*c + 3*a^2*b^2*c^2 + 8*a^2*b*c^3 - 8*a^2*c^4 - 10*a*b^5 - 30*a*b^4*c + 8*a*b^3*c^2 + 10*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 15*b^6 - 8*b^5*c - 8*b^4*c^2 + 30*b^3*c^3 - 8*b^2*c^4 - 10*b*c^5 + 15*c^6) := by
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
  have hn : 0 ≤ (15*a^6 - 8*a^5*b - 10*a^5*c - 8*a^4*b^2 - 30*a^4*b*c - 8*a^4*c^2 + 30*a^3*b^3 + 8*a^3*b^2*c + 10*a^3*b*c^2 + 30*a^3*c^3 - 8*a^2*b^4 + 10*a^2*b^3*c + 3*a^2*b^2*c^2 + 8*a^2*b*c^3 - 8*a^2*c^4 - 10*a*b^5 - 30*a*b^4*c + 8*a*b^3*c^2 + 10*a*b^2*c^3 - 30*a*b*c^4 - 8*a*c^5 + 15*b^6 - 8*b^5*c - 8*b^4*c^2 + 30*b^3*c^3 - 8*b^2*c^4 - 10*b*c^5 + 15*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * a + b) * (5 * a - b) / (b + c) + (3 * b + c) * (5 * b - c) / (c + a) + (3 * c + a) * (5 * c - a) / (a + b) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
