-- Prove2me | solution 1 for WorkbookSource.base_56185
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:46.290733+00:00
-- url     : https://prove2.me/submissions/3a56a326-2322-45a5-a5dd-9a5df3482c9c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / (b + c) + 1 / 2) * (b^2 / (c + a) + 1 / 2) * (c^2 / (a + b) + 1 / 2) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6/9 + 11*a^5*b/27 + 11*a^5*c/27 + 26*a^4*b^2/27 - 14*a^4*b*c/27 + 26*a^4*c^2/27 + 14*a^3*b^3/9 - 61*a^3*b^2*c/27 - 61*a^3*b*c^2/27 + 14*a^3*c^3/9 + 26*a^2*b^4/27 - 61*a^2*b^3*c/27 + 14*a^2*b^2*c^2/9 - 61*a^2*b*c^3/27 + 26*a^2*c^4/27 + 11*a*b^5/27 - 14*a*b^4*c/27 - 61*a*b^3*c^2/27 - 61*a*b^2*c^3/27 - 14*a*b*c^4/27 + 11*a*c^5/27 + 2*b^6/9 + 11*b^5*c/27 + 26*b^4*c^2/27 + 14*b^3*c^3/9 + 26*b^2*c^4/27 + 11*b*c^5/27 + 2*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (44/3 : ℝ) * a^4 * (b - a)^2 + (44/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (44/3 : ℝ) * a^4 * (c - b)^2 + (1130/27 : ℝ) * a^3 * (b - a)^3 + (565/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (491/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (454/27 : ℝ) * a^3 * (c - b)^3 + (1252/27 : ℝ) * a^2 * (b - a)^4 + (2504/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (803/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1157/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (238/27 : ℝ) * a^2 * (c - b)^4 + (640/27 : ℝ) * a^1 * (b - a)^5 + (1600/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1814/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1121/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (383/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (58/27 : ℝ) * a^1 * (c - b)^5 + (128/27 : ℝ) * (b - a)^6 + (128/9 : ℝ) * (b - a)^5 * (c - b)^1 + (508/27 : ℝ) * (b - a)^4 * (c - b)^2 + (376/27 : ℝ) * (b - a)^3 * (c - b)^3 + (19/3 : ℝ) * (b - a)^2 * (c - b)^4 + (47/27 : ℝ) * (b - a)^1 * (c - b)^5 + (2/9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6/9 + 11*a^5*b/27 + 11*a^5*c/27 + 26*a^4*b^2/27 - 14*a^4*b*c/27 + 26*a^4*c^2/27 + 14*a^3*b^3/9 - 61*a^3*b^2*c/27 - 61*a^3*b*c^2/27 + 14*a^3*c^3/9 + 26*a^2*b^4/27 - 61*a^2*b^3*c/27 + 14*a^2*b^2*c^2/9 - 61*a^2*b*c^3/27 + 26*a^2*c^4/27 + 11*a*b^5/27 - 14*a*b^4*c/27 - 61*a*b^3*c^2/27 - 61*a*b^2*c^3/27 - 14*a*b*c^4/27 + 11*a*c^5/27 + 2*b^6/9 + 11*b^5*c/27 + 26*b^4*c^2/27 + 14*b^3*c^3/9 + 26*b^2*c^4/27 + 11*b*c^5/27 + 2*c^6/9) := by
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
  have he : (2*a^4 + 4*a^3*b^2 + 2*a^3*b + 4*a^3*c^2 + 2*a^3*c + 4*a^2*b^3 + 8*a^2*b^2*c^2 + 2*a^2*b*c - 7*a^2*b + 4*a^2*c^3 - 7*a^2*c + 2*a*b^3 + 2*a*b^2*c - 7*a*b^2 + 2*a*b*c^2 - 14*a*b*c + 2*a*c^3 - 7*a*c^2 + 2*b^4 + 4*b^3*c^2 + 2*b^3*c + 4*b^2*c^3 - 7*b^2*c + 2*b*c^3 - 7*b*c^2 + 2*c^4) = (2*a^6/9 + 11*a^5*b/27 + 11*a^5*c/27 + 26*a^4*b^2/27 - 14*a^4*b*c/27 + 26*a^4*c^2/27 + 14*a^3*b^3/9 - 61*a^3*b^2*c/27 - 61*a^3*b*c^2/27 + 14*a^3*c^3/9 + 26*a^2*b^4/27 - 61*a^2*b^3*c/27 + 14*a^2*b^2*c^2/9 - 61*a^2*b*c^3/27 + 26*a^2*c^4/27 + 11*a*b^5/27 - 14*a*b^4*c/27 - 61*a*b^3*c^2/27 - 61*a*b^2*c^3/27 - 14*a*b*c^4/27 + 11*a*c^5/27 + 2*b^6/9 + 11*b^5*c/27 + 26*b^4*c^2/27 + 14*b^3*c^3/9 + 26*b^2*c^4/27 + 11*b*c^5/27 + 2*c^6/9) := by
    linear_combination (-2*a^5/9 - 5*a^4*b/27 - 5*a^4*c/27 - 2*a^4/3 - 7*a^3*b^2/9 + 8*a^3*b*c/9 + a^3*b/9 - 7*a^3*c^2/9 + a^3*c/9 - 7*a^2*b^3/9 + 58*a^2*b^2*c/27 + 14*a^2*b^2/9 + 58*a^2*b*c^2/27 + 22*a^2*b*c/9 + 7*a^2*b/3 - 7*a^2*c^3/9 + 14*a^2*c^2/9 + 7*a^2*c/3 - 5*a*b^4/27 + 8*a*b^3*c/9 + a*b^3/9 + 58*a*b^2*c^2/27 + 22*a*b^2*c/9 + 7*a*b^2/3 + 8*a*b*c^3/9 + 22*a*b*c^2/9 + 14*a*b*c/3 - 5*a*c^4/27 + a*c^3/9 + 7*a*c^2/3 - 2*b^5/9 - 5*b^4*c/27 - 2*b^4/3 - 7*b^3*c^2/9 + b^3*c/9 - 7*b^2*c^3/9 + 14*b^2*c^2/9 + 7*b^2*c/3 - 5*b*c^4/27 + b*c^3/9 + 7*b*c^2/3 - 2*c^5/9 - 2*c^4/3) * habc
  have hn : 0 ≤ (2*a^4 + 4*a^3*b^2 + 2*a^3*b + 4*a^3*c^2 + 2*a^3*c + 4*a^2*b^3 + 8*a^2*b^2*c^2 + 2*a^2*b*c - 7*a^2*b + 4*a^2*c^3 - 7*a^2*c + 2*a*b^3 + 2*a*b^2*c - 7*a*b^2 + 2*a*b*c^2 - 14*a*b*c + 2*a*c^3 - 7*a*c^2 + 2*b^4 + 4*b^3*c^2 + 2*b^3*c + 4*b^2*c^3 - 7*b^2*c + 2*b*c^3 - 7*b*c^2 + 2*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 / (b + c) + 1 / 2) * (b^2 / (c + a) + 1 / 2) * (c^2 / (a + b) + 1 / 2) ≥ 1) := @solution
#print axioms solution
