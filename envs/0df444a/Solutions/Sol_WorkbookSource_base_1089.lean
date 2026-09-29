-- Prove2me | solution 1 for WorkbookSource.base_1089
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:25.092066+00:00
-- url     : https://prove2.me/submissions/c6799537-c0c6-4356-998d-2bca40fa3e1a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * b + a) + b^2 / (2 * c + b) + c^2 / (2 * a + c)) ≥ (a^2 / (2 * a + b) + b^2 / (2 * b + c) + c^2 / (2 * c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b^2 + 10*a^5*b*c + 4*a^5*c^2 - 4*a^4*b^2*c + 21*a^4*b*c^2 + 10*a^4*c^3 + 10*a^3*b^4 - 10*a^3*b^3*c - 35*a^3*b^2*c^2 - 10*a^3*b*c^3 + 4*a^2*b^5 + 21*a^2*b^4*c - 35*a^2*b^3*c^2 - 35*a^2*b^2*c^3 - 4*a^2*b*c^4 + 4*a^2*c^5 + 10*a*b^5*c - 4*a*b^4*c^2 - 10*a*b^3*c^3 + 21*a*b^2*c^4 + 10*a*b*c^5 + 4*b^5*c^2 + 10*b^3*c^4 + 4*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^5 * (b - a)^2 + (162 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (162 : ℝ) * a^5 * (c - b)^2 + (567 : ℝ) * a^4 * (b - a)^3 + (918 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (837 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (243 : ℝ) * a^4 * (c - b)^3 + (765 : ℝ) * a^3 * (b - a)^4 + (1710 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (1755 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (810 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (117 : ℝ) * a^3 * (c - b)^4 + (495 : ℝ) * a^2 * (b - a)^5 + (1400 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (1684 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (991 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (248 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^2 * (c - b)^5 + (153 : ℝ) * a^1 * (b - a)^6 + (514 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (712 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (494 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (161 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (18 : ℝ) * (b - a)^7 + (68 : ℝ) * (b - a)^6 * (c - b)^1 + (104 : ℝ) * (b - a)^5 * (c - b)^2 + (80 : ℝ) * (b - a)^4 * (c - b)^3 + (30 : ℝ) * (b - a)^3 * (c - b)^4 + (4 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*b^2 + 10*a^5*b*c + 4*a^5*c^2 - 4*a^4*b^2*c + 21*a^4*b*c^2 + 10*a^4*c^3 + 10*a^3*b^4 - 10*a^3*b^3*c - 35*a^3*b^2*c^2 - 10*a^3*b*c^3 + 4*a^2*b^5 + 21*a^2*b^4*c - 35*a^2*b^3*c^2 - 35*a^2*b^2*c^3 - 4*a^2*b*c^4 + 4*a^2*c^5 + 10*a*b^5*c - 4*a*b^4*c^2 - 10*a*b^3*c^3 + 21*a*b^2*c^4 + 10*a*b*c^5 + 4*b^5*c^2 + 10*b^3*c^4 + 4*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^5 * (c - a)^2 + (162 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (162 : ℝ) * a^5 * (b - c)^2 + (567 : ℝ) * a^4 * (c - a)^3 + (783 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (702 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (243 : ℝ) * a^4 * (b - c)^3 + (765 : ℝ) * a^3 * (c - a)^4 + (1350 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (1215 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (630 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (117 : ℝ) * a^3 * (b - c)^4 + (495 : ℝ) * a^2 * (c - a)^5 + (1075 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (1034 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (611 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (193 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (18 : ℝ) * a^2 * (b - c)^5 + (153 : ℝ) * a^1 * (c - a)^6 + (404 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (437 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (274 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (106 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (18 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (18 : ℝ) * (c - a)^7 + (58 : ℝ) * (c - a)^6 * (b - c)^1 + (74 : ℝ) * (c - a)^5 * (b - c)^2 + (50 : ℝ) * (c - a)^4 * (b - c)^3 + (20 : ℝ) * (c - a)^3 * (b - c)^4 + (4 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b^2 + 10*a^5*b*c + 4*a^5*c^2 - 4*a^4*b^2*c + 21*a^4*b*c^2 + 10*a^4*c^3 + 10*a^3*b^4 - 10*a^3*b^3*c - 35*a^3*b^2*c^2 - 10*a^3*b*c^3 + 4*a^2*b^5 + 21*a^2*b^4*c - 35*a^2*b^3*c^2 - 35*a^2*b^2*c^3 - 4*a^2*b*c^4 + 4*a^2*c^5 + 10*a*b^5*c - 4*a*b^4*c^2 - 10*a*b^3*c^3 + 21*a*b^2*c^4 + 10*a*b*c^5 + 4*b^5*c^2 + 10*b^3*c^4 + 4*b^2*c^5) := by
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
  have hn : 0 ≤ (4*a^5*b^2 + 10*a^5*b*c + 4*a^5*c^2 - 4*a^4*b^2*c + 21*a^4*b*c^2 + 10*a^4*c^3 + 10*a^3*b^4 - 10*a^3*b^3*c - 35*a^3*b^2*c^2 - 10*a^3*b*c^3 + 4*a^2*b^5 + 21*a^2*b^4*c - 35*a^2*b^3*c^2 - 35*a^2*b^2*c^3 - 4*a^2*b*c^4 + 4*a^2*c^5 + 10*a*b^5*c - 4*a*b^4*c^2 - 10*a*b^3*c^3 + 21*a*b^2*c^4 + 10*a*b*c^5 + 4*b^5*c^2 + 10*b^3*c^4 + 4*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * b + a) + b^2 / (2 * c + b) + c^2 / (2 * a + c)) ≥ (a^2 / (2 * a + b) + b^2 / (2 * b + c) + c^2 / (2 * c + a))) := @solution
#print axioms solution
