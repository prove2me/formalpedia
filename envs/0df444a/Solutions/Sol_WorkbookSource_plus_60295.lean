-- Prove2me | solution 1 for WorkbookSource.plus_60295
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:46.613156+00:00
-- url     : https://prove2.me/submissions/7a0dc191-b05a-4dfe-bb9a-95e6c858b179

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2 + 3 * c^2) * (b^2 + 2 * c^2 + 3 * a^2) * (c^2 + 2 * a^2 + 3 * b^2) ≥ 8 / 9 * (a * b + b * c + c * a) * (a + b + c)^4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (54*a^6 - 8*a^5*b - 8*a^5*c + 175*a^4*b^2 - 72*a^4*b*c + 193*a^4*c^2 - 48*a^3*b^3 - 176*a^3*b^2*c - 176*a^3*b*c^2 - 48*a^3*c^3 + 193*a^2*b^4 - 176*a^2*b^3*c + 198*a^2*b^2*c^2 - 176*a^2*b*c^3 + 175*a^2*c^4 - 8*a*b^5 - 72*a*b^4*c - 176*a*b^3*c^2 - 176*a*b^2*c^3 - 72*a*b*c^4 - 8*a*c^5 + 54*b^6 - 8*b^5*c + 175*b^4*c^2 - 48*b^3*c^3 + 193*b^2*c^4 - 8*b*c^5 + 54*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1296 : ℝ) * a^4 * (b - a)^2 + (1296 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1296 : ℝ) * a^4 * (c - b)^2 + (3528 : ℝ) * a^3 * (b - a)^3 + (5364 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (5148 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (1656 : ℝ) * a^3 * (c - b)^3 + (3834 : ℝ) * a^2 * (b - a)^4 + (7812 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (8586 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (4608 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1026 : ℝ) * a^2 * (c - b)^4 + (1960 : ℝ) * a^1 * (b - a)^5 + (4990 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (6460 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4628 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1814 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (308 : ℝ) * a^1 * (c - b)^5 + (412 : ℝ) * (b - a)^6 + (1254 : ℝ) * (b - a)^5 * (c - b)^1 + (1919 : ℝ) * (b - a)^4 * (c - b)^2 + (1724 : ℝ) * (b - a)^3 * (c - b)^3 + (963 : ℝ) * (b - a)^2 * (c - b)^4 + (316 : ℝ) * (b - a)^1 * (c - b)^5 + (54 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (54*a^6 - 8*a^5*b - 8*a^5*c + 175*a^4*b^2 - 72*a^4*b*c + 193*a^4*c^2 - 48*a^3*b^3 - 176*a^3*b^2*c - 176*a^3*b*c^2 - 48*a^3*c^3 + 193*a^2*b^4 - 176*a^2*b^3*c + 198*a^2*b^2*c^2 - 176*a^2*b*c^3 + 175*a^2*c^4 - 8*a*b^5 - 72*a*b^4*c - 176*a*b^3*c^2 - 176*a*b^2*c^3 - 72*a*b*c^4 - 8*a*c^5 + 54*b^6 - 8*b^5*c + 175*b^4*c^2 - 48*b^3*c^3 + 193*b^2*c^4 - 8*b*c^5 + 54*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1296 : ℝ) * a^4 * (c - a)^2 + (1296 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1296 : ℝ) * a^4 * (b - c)^2 + (3528 : ℝ) * a^3 * (c - a)^3 + (5220 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (5004 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (1656 : ℝ) * a^3 * (b - c)^3 + (3834 : ℝ) * a^2 * (c - a)^4 + (7524 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (8154 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (4464 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1026 : ℝ) * a^2 * (b - c)^4 + (1960 : ℝ) * a^1 * (c - a)^5 + (4810 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (6100 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (4412 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1778 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (308 : ℝ) * a^1 * (b - c)^5 + (412 : ℝ) * (c - a)^6 + (1218 : ℝ) * (c - a)^5 * (b - c)^1 + (1829 : ℝ) * (c - a)^4 * (b - c)^2 + (1652 : ℝ) * (c - a)^3 * (b - c)^3 + (945 : ℝ) * (c - a)^2 * (b - c)^4 + (316 : ℝ) * (c - a)^1 * (b - c)^5 + (54 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (54*a^6 - 8*a^5*b - 8*a^5*c + 175*a^4*b^2 - 72*a^4*b*c + 193*a^4*c^2 - 48*a^3*b^3 - 176*a^3*b^2*c - 176*a^3*b*c^2 - 48*a^3*c^3 + 193*a^2*b^4 - 176*a^2*b^3*c + 198*a^2*b^2*c^2 - 176*a^2*b*c^3 + 175*a^2*c^4 - 8*a*b^5 - 72*a*b^4*c - 176*a*b^3*c^2 - 176*a*b^2*c^3 - 72*a*b*c^4 - 8*a*c^5 + 54*b^6 - 8*b^5*c + 175*b^4*c^2 - 48*b^3*c^3 + 193*b^2*c^4 - 8*b*c^5 + 54*c^6) := by
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
  have hn : 0 ≤ (54*a^6 - 8*a^5*b - 8*a^5*c + 175*a^4*b^2 - 72*a^4*b*c + 193*a^4*c^2 - 48*a^3*b^3 - 176*a^3*b^2*c - 176*a^3*b*c^2 - 48*a^3*c^3 + 193*a^2*b^4 - 176*a^2*b^3*c + 198*a^2*b^2*c^2 - 176*a^2*b*c^3 + 175*a^2*c^4 - 8*a*b^5 - 72*a*b^4*c - 176*a*b^3*c^2 - 176*a*b^2*c^3 - 72*a*b*c^4 - 8*a*c^5 + 54*b^6 - 8*b^5*c + 175*b^4*c^2 - 48*b^3*c^3 + 193*b^2*c^4 - 8*b*c^5 + 54*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 2 * b^2 + 3 * c^2) * (b^2 + 2 * c^2 + 3 * a^2) * (c^2 + 2 * a^2 + 3 * b^2) ≥ 8 / 9 * (a * b + b * c + c * a) * (a + b + c)^4) := @solution
#print axioms solution
