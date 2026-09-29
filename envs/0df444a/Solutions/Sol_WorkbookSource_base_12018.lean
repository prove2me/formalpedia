-- Prove2me | solution 1 for WorkbookSource.base_12018
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:37.741113+00:00
-- url     : https://prove2.me/submissions/d5c37b07-cb4c-4396-8bad-8a1f2bb0016f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (a + 2 * b^2) + b^2 / (b + 2 * c^2) + c^2 / (c + 2 * a^2) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b/9 + 8*a^4*b^2/9 + 8*a^4*b*c/27 + 8*a^4*c^2/3 - 8*a^3*b^3/9 + 4*a^3*b^2*c/9 - 4*a^3*b*c^2/3 - 8*a^3*c^3/9 + 8*a^2*b^4/3 - 4*a^2*b^3*c/3 - 68*a^2*b^2*c^2/9 + 4*a^2*b*c^3/9 + 8*a^2*c^4/9 + 8*a*b^4*c/27 + 4*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 8*a*b*c^4/27 + 4*a*c^5/9 + 4*b^5*c/9 + 8*b^4*c^2/9 - 8*b^3*c^3/9 + 8*b^2*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (44/3 : ℝ) * a^4 * (b - a)^2 + (44/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (44/3 : ℝ) * a^4 * (c - b)^2 + (1120/27 : ℝ) * a^3 * (b - a)^3 + (596/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (532/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (464/27 : ℝ) * a^3 * (c - b)^3 + (1148/27 : ℝ) * a^2 * (b - a)^4 + (2512/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (832/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1132/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (164/27 : ℝ) * a^2 * (c - b)^4 + (508/27 : ℝ) * a^1 * (b - a)^5 + (1396/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (536/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (908/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (212/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * a^1 * (c - b)^5 + (28/9 : ℝ) * (b - a)^6 + (92/9 : ℝ) * (b - a)^5 * (c - b)^1 + (128/9 : ℝ) * (b - a)^4 * (c - b)^2 + (88/9 : ℝ) * (b - a)^3 * (c - b)^3 + (8/3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*b/9 + 8*a^4*b^2/9 + 8*a^4*b*c/27 + 8*a^4*c^2/3 - 8*a^3*b^3/9 + 4*a^3*b^2*c/9 - 4*a^3*b*c^2/3 - 8*a^3*c^3/9 + 8*a^2*b^4/3 - 4*a^2*b^3*c/3 - 68*a^2*b^2*c^2/9 + 4*a^2*b*c^3/9 + 8*a^2*c^4/9 + 8*a*b^4*c/27 + 4*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 8*a*b*c^4/27 + 4*a*c^5/9 + 4*b^5*c/9 + 8*b^4*c^2/9 - 8*b^3*c^3/9 + 8*b^2*c^4/3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (44/3 : ℝ) * a^4 * (c - a)^2 + (44/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (44/3 : ℝ) * a^4 * (b - c)^2 + (1120/27 : ℝ) * a^3 * (c - a)^3 + (524/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (460/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (464/27 : ℝ) * a^3 * (b - c)^3 + (1148/27 : ℝ) * a^2 * (c - a)^4 + (2080/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (616/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (916/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (164/27 : ℝ) * a^2 * (b - c)^4 + (508/27 : ℝ) * a^1 * (c - a)^5 + (1144/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (368/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (620/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (176/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/9 : ℝ) * a^1 * (b - c)^5 + (28/9 : ℝ) * (c - a)^6 + (76/9 : ℝ) * (c - a)^5 * (b - c)^1 + (88/9 : ℝ) * (c - a)^4 * (b - c)^2 + (64/9 : ℝ) * (c - a)^3 * (b - c)^3 + (28/9 : ℝ) * (c - a)^2 * (b - c)^4 + (4/9 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b/9 + 8*a^4*b^2/9 + 8*a^4*b*c/27 + 8*a^4*c^2/3 - 8*a^3*b^3/9 + 4*a^3*b^2*c/9 - 4*a^3*b*c^2/3 - 8*a^3*c^3/9 + 8*a^2*b^4/3 - 4*a^2*b^3*c/3 - 68*a^2*b^2*c^2/9 + 4*a^2*b*c^3/9 + 8*a^2*c^4/9 + 8*a*b^4*c/27 + 4*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 8*a*b*c^4/27 + 4*a*c^5/9 + 4*b^5*c/9 + 8*b^4*c^2/9 - 8*b^3*c^3/9 + 8*b^2*c^4/3) := by
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
  have he : (2*a^4*b + 4*a^4*c^2 + 2*a^3*b^2 - 2*a^3*b - 4*a^3*c^2 + 4*a^2*b^4 - 4*a^2*b^3 - 8*a^2*b^2*c^2 + a^2*b*c + 2*a^2*c^3 + a*b^2*c + a*b*c^2 - a*b*c + 2*a*c^4 - 2*a*c^3 + 2*b^4*c + 2*b^3*c^2 - 2*b^3*c + 4*b^2*c^4 - 4*b^2*c^3) = (4*a^5*b/9 + 8*a^4*b^2/9 + 8*a^4*b*c/27 + 8*a^4*c^2/3 - 8*a^3*b^3/9 + 4*a^3*b^2*c/9 - 4*a^3*b*c^2/3 - 8*a^3*c^3/9 + 8*a^2*b^4/3 - 4*a^2*b^3*c/3 - 68*a^2*b^2*c^2/9 + 4*a^2*b*c^3/9 + 8*a^2*c^4/9 + 8*a*b^4*c/27 + 4*a*b^3*c^2/9 - 4*a*b^2*c^3/3 + 8*a*b*c^4/27 + 4*a*c^5/9 + 4*b^5*c/9 + 8*b^4*c^2/9 - 8*b^3*c^3/9 + 8*b^2*c^4/3) := by
    linear_combination (-4*a^4*b/9 - 4*a^3*b^2/9 + 4*a^3*b*c/27 + 2*a^3*b/3 + 4*a^3*c^2/3 + 4*a^2*b^3/3 - 4*a^2*b^2*c/27 - 4*a^2*b*c^2/27 - 2*a^2*b*c/9 - 4*a^2*c^3/9 + 4*a*b^3*c/27 - 4*a*b^2*c^2/27 - 2*a*b^2*c/9 + 4*a*b*c^3/27 - 2*a*b*c^2/9 + a*b*c/3 - 4*a*c^4/9 + 2*a*c^3/3 - 4*b^4*c/9 - 4*b^3*c^2/9 + 2*b^3*c/3 + 4*b^2*c^3/3) * habc
  have hn : 0 ≤ (2*a^4*b + 4*a^4*c^2 + 2*a^3*b^2 - 2*a^3*b - 4*a^3*c^2 + 4*a^2*b^4 - 4*a^2*b^3 - 8*a^2*b^2*c^2 + a^2*b*c + 2*a^2*c^3 + a*b^2*c + a*b*c^2 - a*b*c + 2*a*c^4 - 2*a*c^3 + 2*b^4*c + 2*b^3*c^2 - 2*b^3*c + 4*b^2*c^4 - 4*b^2*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 / (a + 2 * b^2) + b^2 / (b + 2 * c^2) + c^2 / (c + 2 * a^2) ≥ 1) := @solution
#print axioms solution
