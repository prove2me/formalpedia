-- Prove2me | solution 1 for WorkbookSource.base_31228
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:26:57.646247+00:00
-- url     : https://prove2.me/submissions/faf5c1e5-1159-4bac-a8f9-d968e4fed177

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^3 + b^2 / c^3 + c^2 / a^3) ≥ (a / b^2 + b / c^2 + c / a^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c^3 - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a*b^3*c^4 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^6 * (b - a)^2 + (4 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^6 * (c - b)^2 + (18 : ℝ) * a^5 * (b - a)^3 + (33 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (27 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (6 : ℝ) * a^5 * (c - b)^3 + (34 : ℝ) * a^4 * (b - a)^4 + (88 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (87 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (33 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^4 * (c - b)^4 + (35 : ℝ) * a^3 * (b - a)^5 + (114 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (140 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (76 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (17 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^3 * (c - b)^5 + (21 : ℝ) * a^2 * (b - a)^6 + (81 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (120 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (84 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (7 : ℝ) * a^1 * (b - a)^7 + (31 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (54 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (46 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (19 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^8 + (5 : ℝ) * (b - a)^7 * (c - b)^1 + (10 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (5 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c^3 - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a*b^3*c^4 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^6 * (c - a)^2 + (4 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^6 * (b - c)^2 + (18 : ℝ) * a^5 * (c - a)^3 + (21 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (15 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (6 : ℝ) * a^5 * (b - c)^3 + (34 : ℝ) * a^4 * (c - a)^4 + (48 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (27 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (13 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^4 * (b - c)^4 + (35 : ℝ) * a^3 * (c - a)^5 + (61 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (34 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (10 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (1 : ℝ) * a^3 * (b - c)^5 + (21 : ℝ) * a^2 * (c - a)^6 + (45 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (30 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (6 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (7 : ℝ) * a^1 * (c - a)^7 + (18 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (4 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1 : ℝ) * (c - a)^8 + (3 : ℝ) * (c - a)^7 * (b - c)^1 + (3 : ℝ) * (c - a)^6 * (b - c)^2 + (1 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c^3 - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a*b^3*c^4 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^5*c^3 - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a*b^3*c^4 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b^3 + b^2 / c^3 + c^2 / a^3) ≥ (a / b^2 + b / c^2 + c / a^2)) := @solution
#print axioms solution
