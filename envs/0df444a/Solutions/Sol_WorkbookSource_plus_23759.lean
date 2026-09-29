-- Prove2me | solution 1 for WorkbookSource.plus_23759
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:09.29426+00:00
-- url     : https://prove2.me/submissions/fd1e9b16-01da-441d-9c10-4a68ae7b9273

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 1) ≥ 12 * (a^2 + b^2 + c^2) / (a + b + c)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c^2 + 2*a^5*b*c^2 + 2*a^5*c^3 + a^4*b^4 - 10*a^4*b^2*c^2 + 2*a^4*b*c^3 + a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^6 + 2*a^2*b^5*c - 10*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 2*a*b^3*c^4 + 2*a*b^2*c^5 + b^4*c^4 + 2*b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * a^6 * (b - a)^2 + (28 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (28 : ℝ) * a^6 * (c - b)^2 + (124 : ℝ) * a^5 * (b - a)^3 + (222 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (186 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (44 : ℝ) * a^5 * (c - b)^3 + (229 : ℝ) * a^4 * (b - a)^4 + (578 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (577 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (228 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (29 : ℝ) * a^4 * (c - b)^4 + (226 : ℝ) * a^3 * (b - a)^5 + (722 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (892 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (496 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (120 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^3 * (c - b)^5 + (125 : ℝ) * a^2 * (b - a)^6 + (476 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (711 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (514 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (182 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (28 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (36 : ℝ) * a^1 * (b - a)^7 + (158 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (278 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (248 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (116 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (20 : ℝ) * (b - a)^7 * (c - b)^1 + (41 : ℝ) * (b - a)^6 * (c - b)^2 + (44 : ℝ) * (b - a)^5 * (c - b)^3 + (26 : ℝ) * (b - a)^4 * (c - b)^4 + (8 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c^2 + 2*a^5*b*c^2 + 2*a^5*c^3 + a^4*b^4 - 10*a^4*b^2*c^2 + 2*a^4*b*c^3 + a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^6 + 2*a^2*b^5*c - 10*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 2*a*b^3*c^4 + 2*a*b^2*c^5 + b^4*c^4 + 2*b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * a^6 * (c - a)^2 + (28 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (28 : ℝ) * a^6 * (b - c)^2 + (124 : ℝ) * a^5 * (c - a)^3 + (150 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (114 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (44 : ℝ) * a^5 * (b - c)^3 + (229 : ℝ) * a^4 * (c - a)^4 + (338 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (217 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (108 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (29 : ℝ) * a^4 * (b - c)^4 + (226 : ℝ) * a^3 * (c - a)^5 + (408 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (264 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (108 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (46 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (10 : ℝ) * a^3 * (b - c)^5 + (125 : ℝ) * a^2 * (c - a)^6 + (274 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (206 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (70 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (21 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (8 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^2 * (b - c)^6 + (36 : ℝ) * a^1 * (c - a)^7 + (94 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (86 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (32 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (4 : ℝ) * (c - a)^8 + (12 : ℝ) * (c - a)^7 * (b - c)^1 + (13 : ℝ) * (c - a)^6 * (b - c)^2 + (6 : ℝ) * (c - a)^5 * (b - c)^3 + (1 : ℝ) * (c - a)^4 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c^2 + 2*a^5*b*c^2 + 2*a^5*c^3 + a^4*b^4 - 10*a^4*b^2*c^2 + 2*a^4*b*c^3 + a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^6 + 2*a^2*b^5*c - 10*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 2*a*b^3*c^4 + 2*a*b^2*c^5 + b^4*c^4 + 2*b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*c^2 + 2*a^5*b*c^2 + 2*a^5*c^3 + a^4*b^4 - 10*a^4*b^2*c^2 + 2*a^4*b*c^3 + a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^6 + 2*a^2*b^5*c - 10*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 2*a*b^3*c^4 + 2*a*b^2*c^5 + b^4*c^4 + 2*b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 1) ≥ 12 * (a^2 + b^2 + c^2) / (a + b + c)^2) := @solution
#print axioms solution
