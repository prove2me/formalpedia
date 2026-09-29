-- Prove2me | solution 1 for WorkbookSource.base_834
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:20.061356+00:00
-- url     : https://prove2.me/submissions/42e099dc-eadd-4f13-a77c-252a2303abf9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) + 1 / (a * b * c) ≥ 5 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b/27 + 2*a^5*c/27 + 8*a^4*b^2/27 + 16*a^4*b*c/27 + 8*a^4*c^2/27 + 4*a^3*b^3/9 + 11*a^3*b^2*c/27 - 43*a^3*b*c^2/27 + 4*a^3*c^3/9 + 8*a^2*b^4/27 - 43*a^2*b^3*c/27 - 16*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 + 8*a^2*c^4/27 + 2*a*b^5/27 + 16*a*b^4*c/27 + 11*a*b^3*c^2/27 - 43*a*b^2*c^3/27 + 16*a*b*c^4/27 + 2*a*c^5/27 + 2*b^5*c/27 + 8*b^4*c^2/27 + 4*b^3*c^3/9 + 8*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (416/27 : ℝ) * a^3 * (b - a)^3 + (199/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (167/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (160/27 : ℝ) * a^3 * (c - b)^3 + (436/27 : ℝ) * a^2 * (b - a)^4 + (818/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (233/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (317/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (52/27 : ℝ) * a^2 * (c - b)^4 + (196/27 : ℝ) * a^1 * (b - a)^5 + (463/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (446/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (233/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (62/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/27 : ℝ) * a^1 * (c - b)^5 + (32/27 : ℝ) * (b - a)^6 + (32/9 : ℝ) * (b - a)^5 * (c - b)^1 + (112/27 : ℝ) * (b - a)^4 * (c - b)^2 + (64/27 : ℝ) * (b - a)^3 * (c - b)^3 + (2/3 : ℝ) * (b - a)^2 * (c - b)^4 + (2/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*b/27 + 2*a^5*c/27 + 8*a^4*b^2/27 + 16*a^4*b*c/27 + 8*a^4*c^2/27 + 4*a^3*b^3/9 + 11*a^3*b^2*c/27 - 43*a^3*b*c^2/27 + 4*a^3*c^3/9 + 8*a^2*b^4/27 - 43*a^2*b^3*c/27 - 16*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 + 8*a^2*c^4/27 + 2*a*b^5/27 + 16*a*b^4*c/27 + 11*a*b^3*c^2/27 - 43*a*b^2*c^3/27 + 16*a*b*c^4/27 + 2*a*c^5/27 + 2*b^5*c/27 + 8*b^4*c^2/27 + 4*b^3*c^3/9 + 8*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (c - a)^2 + (16/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16/3 : ℝ) * a^4 * (b - c)^2 + (416/27 : ℝ) * a^3 * (c - a)^3 + (217/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (185/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (160/27 : ℝ) * a^3 * (b - c)^3 + (436/27 : ℝ) * a^2 * (c - a)^4 + (926/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (287/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (371/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (52/27 : ℝ) * a^2 * (b - c)^4 + (196/27 : ℝ) * a^1 * (c - a)^5 + (517/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (554/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (287/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (62/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/27 : ℝ) * a^1 * (b - c)^5 + (32/27 : ℝ) * (c - a)^6 + (32/9 : ℝ) * (c - a)^5 * (b - c)^1 + (112/27 : ℝ) * (c - a)^4 * (b - c)^2 + (64/27 : ℝ) * (c - a)^3 * (b - c)^3 + (2/3 : ℝ) * (c - a)^2 * (b - c)^4 + (2/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b/27 + 2*a^5*c/27 + 8*a^4*b^2/27 + 16*a^4*b*c/27 + 8*a^4*c^2/27 + 4*a^3*b^3/9 + 11*a^3*b^2*c/27 - 43*a^3*b*c^2/27 + 4*a^3*c^3/9 + 8*a^2*b^4/27 - 43*a^2*b^3*c/27 - 16*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 + 8*a^2*c^4/27 + 2*a*b^5/27 + 16*a*b^4*c/27 + 11*a*b^3*c^2/27 - 43*a*b^2*c^3/27 + 16*a*b*c^4/27 + 2*a*c^5/27 + 2*b^5*c/27 + 8*b^4*c^2/27 + 4*b^3*c^3/9 + 8*b^2*c^4/27 + 2*b*c^5/27) := by
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
  have he : (-a^3*b^2*c - 3*a^3*b*c^2 - 3*a^2*b^3*c - 4*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*b + 2*a^2*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b^2 + 4*a*b*c + 2*a*c^2 + 2*b^2*c + 2*b*c^2) = (2*a^5*b/27 + 2*a^5*c/27 + 8*a^4*b^2/27 + 16*a^4*b*c/27 + 8*a^4*c^2/27 + 4*a^3*b^3/9 + 11*a^3*b^2*c/27 - 43*a^3*b*c^2/27 + 4*a^3*c^3/9 + 8*a^2*b^4/27 - 43*a^2*b^3*c/27 - 16*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 + 8*a^2*c^4/27 + 2*a*b^5/27 + 16*a*b^4*c/27 + 11*a*b^3*c^2/27 - 43*a*b^2*c^3/27 + 16*a*b*c^4/27 + 2*a*c^5/27 + 2*b^5*c/27 + 8*b^4*c^2/27 + 4*b^3*c^3/9 + 8*b^2*c^4/27 + 2*b*c^5/27) := by
    linear_combination (-2*a^4*b/27 - 2*a^4*c/27 - 2*a^3*b^2/9 - 4*a^3*b*c/9 - 2*a^3*b/9 - 2*a^3*c^2/9 - 2*a^3*c/9 - 2*a^2*b^3/9 - 20*a^2*b^2*c/27 - 4*a^2*b^2/9 - 20*a^2*b*c^2/27 - 8*a^2*b*c/9 - 2*a^2*b/3 - 2*a^2*c^3/9 - 4*a^2*c^2/9 - 2*a^2*c/3 - 2*a*b^4/27 - 4*a*b^3*c/9 - 2*a*b^3/9 - 20*a*b^2*c^2/27 - 8*a*b^2*c/9 - 2*a*b^2/3 - 4*a*b*c^3/9 - 8*a*b*c^2/9 - 4*a*b*c/3 - 2*a*c^4/27 - 2*a*c^3/9 - 2*a*c^2/3 - 2*b^4*c/27 - 2*b^3*c^2/9 - 2*b^3*c/9 - 2*b^2*c^3/9 - 4*b^2*c^2/9 - 2*b^2*c/3 - 2*b*c^4/27 - 2*b*c^3/9 - 2*b*c^2/3) * hab
  have hn : 0 ≤ (-a^3*b^2*c - 3*a^3*b*c^2 - 3*a^2*b^3*c - 4*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*b + 2*a^2*c - a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b^2 + 4*a*b*c + 2*a*c^2 + 2*b^2*c + 2*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a + b) + b / (b + c) + c / (c + a) + 1 / (a * b * c) ≥ 5 / 2) := @solution
#print axioms solution
