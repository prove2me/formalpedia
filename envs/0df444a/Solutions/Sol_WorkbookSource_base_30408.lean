-- Prove2me | solution 1 for WorkbookSource.base_30408
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:19:11.471387+00:00
-- url     : https://prove2.me/submissions/fc18818f-c049-4bcd-990a-12119bb45139

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (a^2 + 2) + b / (b^2 + 2) + c / (c^2 + 2) ≤ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (32*a^6/729 + 22*a^5*b/243 + 22*a^5*c/243 + 46*a^4*b^2/243 - 4*a^4*b*c/243 + 46*a^4*c^2/243 + 208*a^3*b^3/729 - 95*a^3*b^2*c/243 - 95*a^3*b*c^2/243 + 208*a^3*c^3/729 + 46*a^2*b^4/243 - 95*a^2*b^3*c/243 - 22*a^2*b^2*c^2/81 - 95*a^2*b*c^3/243 + 46*a^2*c^4/243 + 22*a*b^5/243 - 4*a*b^4*c/243 - 95*a*b^3*c^2/243 - 95*a*b^2*c^3/243 - 4*a*b*c^4/243 + 22*a*c^5/243 + 32*b^6/729 + 22*b^5*c/243 + 46*b^4*c^2/243 + 208*b^3*c^3/729 + 46*b^2*c^4/243 + 22*b*c^5/243 + 32*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * a^4 * (b - a)^2 + (10/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (10/3 : ℝ) * a^4 * (c - b)^2 + (254/27 : ℝ) * a^3 * (b - a)^3 + (127/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (113/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (106/27 : ℝ) * a^3 * (c - b)^3 + (274/27 : ℝ) * a^2 * (b - a)^4 + (548/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (179/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (263/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (52/27 : ℝ) * a^2 * (c - b)^4 + (134/27 : ℝ) * a^1 * (b - a)^5 + (335/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (128/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (241/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (82/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * a^1 * (c - b)^5 + (680/729 : ℝ) * (b - a)^6 + (680/243 : ℝ) * (b - a)^5 * (c - b)^1 + (910/243 : ℝ) * (b - a)^4 * (c - b)^2 + (2060/729 : ℝ) * (b - a)^3 * (c - b)^3 + (316/243 : ℝ) * (b - a)^2 * (c - b)^4 + (86/243 : ℝ) * (b - a)^1 * (c - b)^5 + (32/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (32*a^6/729 + 22*a^5*b/243 + 22*a^5*c/243 + 46*a^4*b^2/243 - 4*a^4*b*c/243 + 46*a^4*c^2/243 + 208*a^3*b^3/729 - 95*a^3*b^2*c/243 - 95*a^3*b*c^2/243 + 208*a^3*c^3/729 + 46*a^2*b^4/243 - 95*a^2*b^3*c/243 - 22*a^2*b^2*c^2/81 - 95*a^2*b*c^3/243 + 46*a^2*c^4/243 + 22*a*b^5/243 - 4*a*b^4*c/243 - 95*a*b^3*c^2/243 - 95*a*b^2*c^3/243 - 4*a*b*c^4/243 + 22*a*c^5/243 + 32*b^6/729 + 22*b^5*c/243 + 46*b^4*c^2/243 + 208*b^3*c^3/729 + 46*b^2*c^4/243 + 22*b*c^5/243 + 32*c^6/729) := by
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
  have he : (a^2*b^2*c^2 - a^2*b^2*c + 2*a^2*b^2 - a^2*b*c^2 - 2*a^2*b + 2*a^2*c^2 - 2*a^2*c + 4*a^2 - a*b^2*c^2 - 2*a*b^2 - 2*a*c^2 - 4*a + 2*b^2*c^2 - 2*b^2*c + 4*b^2 - 2*b*c^2 - 4*b + 4*c^2 - 4*c + 8) = (32*a^6/729 + 22*a^5*b/243 + 22*a^5*c/243 + 46*a^4*b^2/243 - 4*a^4*b*c/243 + 46*a^4*c^2/243 + 208*a^3*b^3/729 - 95*a^3*b^2*c/243 - 95*a^3*b*c^2/243 + 208*a^3*c^3/729 + 46*a^2*b^4/243 - 95*a^2*b^3*c/243 - 22*a^2*b^2*c^2/81 - 95*a^2*b*c^3/243 + 46*a^2*c^4/243 + 22*a*b^5/243 - 4*a*b^4*c/243 - 95*a*b^3*c^2/243 - 95*a*b^2*c^3/243 - 4*a*b*c^4/243 + 22*a*c^5/243 + 32*b^6/729 + 22*b^5*c/243 + 46*b^4*c^2/243 + 208*b^3*c^3/729 + 46*b^2*c^4/243 + 22*b*c^5/243 + 32*c^6/729) := by
    linear_combination (-32*a^5/729 - 34*a^4*b/729 - 34*a^4*c/729 - 32*a^4/243 - 104*a^3*b^2/729 + 80*a^3*b*c/729 - 2*a^3*b/243 - 104*a^3*c^2/729 - 2*a^3*c/243 - 32*a^3/81 - 104*a^2*b^3/729 + 103*a^2*b^2*c/243 - 34*a^2*b^2/81 + 103*a^2*b*c^2/243 + 28*a^2*b*c/81 + 10*a^2*b/27 - 104*a^2*c^3/729 - 34*a^2*c^2/81 + 10*a^2*c/27 - 32*a^2/27 - 34*a*b^4/729 + 80*a*b^3*c/729 - 2*a*b^3/243 + 103*a*b^2*c^2/243 + 28*a*b^2*c/81 + 10*a*b^2/27 + 80*a*b*c^3/729 + 28*a*b*c^2/81 + 8*a*b*c/27 + 8*a*b/27 - 34*a*c^4/729 - 2*a*c^3/243 + 10*a*c^2/27 + 8*a*c/27 + 4*a/9 - 32*b^5/729 - 34*b^4*c/729 - 32*b^4/243 - 104*b^3*c^2/729 - 2*b^3*c/243 - 32*b^3/81 - 104*b^2*c^3/729 - 34*b^2*c^2/81 + 10*b^2*c/27 - 32*b^2/27 - 34*b*c^4/729 - 2*b*c^3/243 + 10*b*c^2/27 + 8*b*c/27 + 4*b/9 - 32*c^5/729 - 32*c^4/243 - 32*c^3/81 - 32*c^2/27 + 4*c/9 - 8/3) * habc
  have hn : 0 ≤ (a^2*b^2*c^2 - a^2*b^2*c + 2*a^2*b^2 - a^2*b*c^2 - 2*a^2*b + 2*a^2*c^2 - 2*a^2*c + 4*a^2 - a*b^2*c^2 - 2*a*b^2 - 2*a*c^2 - 4*a + 2*b^2*c^2 - 2*b^2*c + 4*b^2 - 2*b*c^2 - 4*b + 4*c^2 - 4*c + 8) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (a^2 + 2) + b / (b^2 + 2) + c / (c^2 + 2) ≤ 1) := @solution
#print axioms solution
