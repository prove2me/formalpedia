-- Prove2me | solution 1 for WorkbookSource.base_22250
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:15.214559+00:00
-- url     : https://prove2.me/submissions/bdfa4cfc-565e-45cd-9958-25843ca66df7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b ^ 2 + 3 * c ^ 2 + 5 * b * c) + b / (c ^ 2 + 3 * a ^ 2 + 5 * c * a) + c / (a ^ 2 + 3 * b ^ 2 + 5 * a * b)) ≥ 1 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6 + 18*a^5*b + 8*a^5*c + 21*a^4*b^2 + 30*a^4*b*c - 3*a^4*c^2 - 5*a^3*b^3 - 23*a^3*b^2*c - 21*a^3*b*c^2 - 5*a^3*c^3 - 3*a^2*b^4 - 21*a^2*b^3*c - 84*a^2*b^2*c^2 - 23*a^2*b*c^3 + 21*a^2*c^4 + 8*a*b^5 + 30*a*b^4*c - 23*a*b^3*c^2 - 21*a*b^2*c^3 + 30*a*b*c^4 + 18*a*c^5 + 3*b^6 + 18*b^5*c + 21*b^4*c^2 - 5*b^3*c^3 - 3*b^2*c^4 + 8*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (321 : ℝ) * a^4 * (b - a)^2 + (321 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (321 : ℝ) * a^4 * (c - b)^2 + (826 : ℝ) * a^3 * (b - a)^3 + (1094 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1184 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (458 : ℝ) * a^3 * (c - b)^3 + (775 : ℝ) * a^2 * (b - a)^4 + (1260 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1473 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (988 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (223 : ℝ) * a^2 * (c - b)^4 + (312 : ℝ) * a^1 * (b - a)^5 + (586 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (726 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (648 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (284 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (44 : ℝ) * a^1 * (c - b)^5 + (45 : ℝ) * (b - a)^6 + (91 : ℝ) * (b - a)^5 * (c - b)^1 + (113 : ℝ) * (b - a)^4 * (c - b)^2 + (123 : ℝ) * (b - a)^3 * (c - b)^3 + (82 : ℝ) * (b - a)^2 * (c - b)^4 + (26 : ℝ) * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^6 + 18*a^5*b + 8*a^5*c + 21*a^4*b^2 + 30*a^4*b*c - 3*a^4*c^2 - 5*a^3*b^3 - 23*a^3*b^2*c - 21*a^3*b*c^2 - 5*a^3*c^3 - 3*a^2*b^4 - 21*a^2*b^3*c - 84*a^2*b^2*c^2 - 23*a^2*b*c^3 + 21*a^2*c^4 + 8*a*b^5 + 30*a*b^4*c - 23*a*b^3*c^2 - 21*a*b^2*c^3 + 30*a*b*c^4 + 18*a*c^5 + 3*b^6 + 18*b^5*c + 21*b^4*c^2 - 5*b^3*c^3 - 3*b^2*c^4 + 8*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (321 : ℝ) * a^4 * (c - a)^2 + (321 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (321 : ℝ) * a^4 * (b - c)^2 + (826 : ℝ) * a^3 * (c - a)^3 + (1384 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1474 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (458 : ℝ) * a^3 * (b - c)^3 + (775 : ℝ) * a^2 * (c - a)^4 + (1840 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (2343 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1278 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (223 : ℝ) * a^2 * (b - c)^4 + (312 : ℝ) * a^1 * (c - a)^5 + (974 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1502 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1134 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (382 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (44 : ℝ) * a^1 * (b - c)^5 + (45 : ℝ) * (c - a)^6 + (179 : ℝ) * (c - a)^5 * (b - c)^1 + (333 : ℝ) * (c - a)^4 * (b - c)^2 + (319 : ℝ) * (c - a)^3 * (b - c)^3 + (156 : ℝ) * (c - a)^2 * (b - c)^4 + (36 : ℝ) * (c - a)^1 * (b - c)^5 + (3 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6 + 18*a^5*b + 8*a^5*c + 21*a^4*b^2 + 30*a^4*b*c - 3*a^4*c^2 - 5*a^3*b^3 - 23*a^3*b^2*c - 21*a^3*b*c^2 - 5*a^3*c^3 - 3*a^2*b^4 - 21*a^2*b^3*c - 84*a^2*b^2*c^2 - 23*a^2*b*c^3 + 21*a^2*c^4 + 8*a*b^5 + 30*a*b^4*c - 23*a*b^3*c^2 - 21*a*b^2*c^3 + 30*a*b*c^4 + 18*a*c^5 + 3*b^6 + 18*b^5*c + 21*b^4*c^2 - 5*b^3*c^3 - 3*b^2*c^4 + 8*b*c^5 + 3*c^6) := by
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
  have hn : 0 ≤ (3*a^6 + 18*a^5*b + 8*a^5*c + 21*a^4*b^2 + 30*a^4*b*c - 3*a^4*c^2 - 5*a^3*b^3 - 23*a^3*b^2*c - 21*a^3*b*c^2 - 5*a^3*c^3 - 3*a^2*b^4 - 21*a^2*b^3*c - 84*a^2*b^2*c^2 - 23*a^2*b*c^3 + 21*a^2*c^4 + 8*a*b^5 + 30*a*b^4*c - 23*a*b^3*c^2 - 21*a*b^2*c^3 + 30*a*b*c^4 + 18*a*c^5 + 3*b^6 + 18*b^5*c + 21*b^4*c^2 - 5*b^3*c^3 - 3*b^2*c^4 + 8*b*c^5 + 3*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b ^ 2 + 3 * c ^ 2 + 5 * b * c) + b / (c ^ 2 + 3 * a ^ 2 + 5 * c * a) + c / (a ^ 2 + 3 * b ^ 2 + 5 * a * b)) ≥ 1 / (a + b + c)) := @solution
#print axioms solution
