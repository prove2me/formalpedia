-- Prove2me | solution 1 for WorkbookSource.base_50076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:43.720499+00:00
-- url     : https://prove2.me/submissions/8c7905da-5a24-4d50-b93f-cd3911777281

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 / b + b^5 / c + c^5 / a) ≥ 1 / 27 * (a + b + c)^4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (27*a^6*c - a^5*b*c - 4*a^4*b^2*c - 4*a^4*b*c^2 - 6*a^3*b^3*c - 12*a^3*b^2*c^2 - 6*a^3*b*c^3 - 4*a^2*b^4*c - 12*a^2*b^3*c^2 - 12*a^2*b^2*c^3 - 4*a^2*b*c^4 + 27*a*b^6 - a*b^5*c - 4*a*b^4*c^2 - 6*a*b^3*c^3 - 4*a*b^2*c^4 - a*b*c^5 + 27*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (243 : ℝ) * a^5 * (b - a)^2 + (243 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (243 : ℝ) * a^5 * (c - b)^2 + (741 : ℝ) * a^4 * (b - a)^3 + (1314 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (1521 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (474 : ℝ) * a^4 * (c - b)^3 + (926 : ℝ) * a^3 * (b - a)^4 + (2392 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (3468 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (2002 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (392 : ℝ) * a^3 * (c - b)^4 + (601 : ℝ) * a^2 * (b - a)^5 + (2110 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (3754 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (3116 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (1193 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (161 : ℝ) * a^2 * (c - b)^5 + (200 : ℝ) * a^1 * (b - a)^6 + (924 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1969 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (2128 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (1206 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (323 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (27 : ℝ) * a^1 * (c - b)^6 + (27 : ℝ) * (b - a)^7 + (162 : ℝ) * (b - a)^6 * (c - b)^1 + (405 : ℝ) * (b - a)^5 * (c - b)^2 + (540 : ℝ) * (b - a)^4 * (c - b)^3 + (405 : ℝ) * (b - a)^3 * (c - b)^4 + (162 : ℝ) * (b - a)^2 * (c - b)^5 + (27 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (27*a^6*c - a^5*b*c - 4*a^4*b^2*c - 4*a^4*b*c^2 - 6*a^3*b^3*c - 12*a^3*b^2*c^2 - 6*a^3*b*c^3 - 4*a^2*b^4*c - 12*a^2*b^3*c^2 - 12*a^2*b^2*c^3 - 4*a^2*b*c^4 + 27*a*b^6 - a*b^5*c - 4*a*b^4*c^2 - 6*a*b^3*c^3 - 4*a*b^2*c^4 - a*b*c^5 + 27*b*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (243 : ℝ) * a^5 * (c - a)^2 + (243 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (243 : ℝ) * a^5 * (b - c)^2 + (741 : ℝ) * a^4 * (c - a)^3 + (909 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (1116 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (474 : ℝ) * a^4 * (b - c)^3 + (926 : ℝ) * a^3 * (c - a)^4 + (1312 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (1848 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (1462 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (392 : ℝ) * a^3 * (b - c)^4 + (601 : ℝ) * a^2 * (c - a)^5 + (895 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (1324 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (1496 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (788 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (161 : ℝ) * a^2 * (b - c)^5 + (200 : ℝ) * a^1 * (c - a)^6 + (276 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (349 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (508 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (396 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (161 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (27 : ℝ) * a^1 * (b - c)^6 + (27 : ℝ) * (c - a)^7 + (27 : ℝ) * (c - a)^6 * (b - c)^1 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (27*a^6*c - a^5*b*c - 4*a^4*b^2*c - 4*a^4*b*c^2 - 6*a^3*b^3*c - 12*a^3*b^2*c^2 - 6*a^3*b*c^3 - 4*a^2*b^4*c - 12*a^2*b^3*c^2 - 12*a^2*b^2*c^3 - 4*a^2*b*c^4 + 27*a*b^6 - a*b^5*c - 4*a*b^4*c^2 - 6*a*b^3*c^3 - 4*a*b^2*c^4 - a*b*c^5 + 27*b*c^6) := by
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
  have hn : 0 ≤ (27*a^6*c - a^5*b*c - 4*a^4*b^2*c - 4*a^4*b*c^2 - 6*a^3*b^3*c - 12*a^3*b^2*c^2 - 6*a^3*b*c^3 - 4*a^2*b^4*c - 12*a^2*b^3*c^2 - 12*a^2*b^2*c^3 - 4*a^2*b*c^4 + 27*a*b^6 - a*b^5*c - 4*a*b^4*c^2 - 6*a*b^3*c^3 - 4*a*b^2*c^4 - a*b*c^5 + 27*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^5 / b + b^5 / c + c^5 / a) ≥ 1 / 27 * (a + b + c)^4) := @solution
#print axioms solution
