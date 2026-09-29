-- Prove2me | solution 1 for WorkbookSource.base_12418
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:24.658246+00:00
-- url     : https://prove2.me/submissions/09380de3-21b6-4899-9a06-3703384b6153

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b ^ 2 / c ^ 2 + b * c ^ 2 / a ^ 2 + c * a ^ 2 / b ^ 2 + a + b + c) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c^3 + a^4*b^4 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + b^4*c^4 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (b - a)^2 + (8 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^6 * (c - b)^2 + (40 : ℝ) * a^5 * (b - a)^3 + (69 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^5 * (c - b)^3 + (83 : ℝ) * a^4 * (b - a)^4 + (196 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (154 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (41 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^4 * (c - b)^4 + (91 : ℝ) * a^3 * (b - a)^5 + (266 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (272 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (112 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (17 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^3 * (c - b)^5 + (55 : ℝ) * a^2 * (b - a)^6 + (189 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (241 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (138 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (34 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (17 : ℝ) * a^1 * (b - a)^7 + (67 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (102 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (74 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (25 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * (b - a)^8 + (9 : ℝ) * (b - a)^7 * (c - b)^1 + (16 : ℝ) * (b - a)^6 * (c - b)^2 + (14 : ℝ) * (b - a)^5 * (c - b)^3 + (6 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c^3 + a^4*b^4 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + b^4*c^4 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (c - a)^2 + (8 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^6 * (b - c)^2 + (40 : ℝ) * a^5 * (c - a)^3 + (51 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (27 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (8 : ℝ) * a^5 * (b - c)^3 + (83 : ℝ) * a^4 * (c - a)^4 + (136 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (64 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (11 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (3 : ℝ) * a^4 * (b - c)^4 + (91 : ℝ) * a^3 * (c - a)^5 + (189 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (118 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (18 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^3 * (b - c)^5 + (55 : ℝ) * a^2 * (c - a)^6 + (141 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (121 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (1 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (17 : ℝ) * a^1 * (c - a)^7 + (52 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (57 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (26 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (2 : ℝ) * (c - a)^8 + (7 : ℝ) * (c - a)^7 * (b - c)^1 + (9 : ℝ) * (c - a)^6 * (b - c)^2 + (5 : ℝ) * (c - a)^5 * (b - c)^3 + (1 : ℝ) * (c - a)^4 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c^3 + a^4*b^4 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + b^4*c^4 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^5*c^3 + a^4*b^4 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + b^4*c^4 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b ^ 2 / c ^ 2 + b * c ^ 2 / a ^ 2 + c * a ^ 2 / b ^ 2 + a + b + c) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)) := @solution
#print axioms solution
