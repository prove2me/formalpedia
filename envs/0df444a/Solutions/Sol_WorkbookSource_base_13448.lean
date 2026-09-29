-- Prove2me | solution 1 for WorkbookSource.base_13448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:11.922575+00:00
-- url     : https://prove2.me/submissions/b46921de-a20b-4f0c-a82a-799b75739951

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (1 / (5 * a ^ 2 + a * b + b * c) + 1 / (5 * b ^ 2 + b * c + c * a) + 1 / (5 * c ^ 2 + c * a + a * b)) ≥ 3 / 7  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (35*a^5*b/9 + 70*a^5*c/9 + 28*a^4*b^2 + 131*a^4*b*c/9 + 187*a^4*c^2/9 - 206*a^3*b^3/9 - 55*a^3*b^2*c/3 + 545*a^3*b*c^2/9 - 206*a^3*c^3/9 + 187*a^2*b^4/9 + 545*a^2*b^3*c/9 - 283*a^2*b^2*c^2 - 55*a^2*b*c^3/3 + 28*a^2*c^4 + 70*a*b^5/9 + 131*a*b^4*c/9 - 55*a*b^3*c^2/3 + 545*a*b^2*c^3/9 + 131*a*b*c^4/9 + 35*a*c^5/9 + 35*b^5*c/9 + 28*b^4*c^2 - 206*b^3*c^3/9 + 187*b^2*c^4/9 + 70*b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (294 : ℝ) * a^4 * (b - a)^2 + (294 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (294 : ℝ) * a^4 * (c - b)^2 + (7286/9 : ℝ) * a^3 * (b - a)^3 + (3733/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (3503/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (3298/9 : ℝ) * a^3 * (c - b)^3 + (2359/3 : ℝ) * a^2 * (b - a)^4 + (4898/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (5008/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (823 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (365/3 : ℝ) * a^2 * (c - b)^4 + (925/3 : ℝ) * a^1 * (b - a)^5 + (2410/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2810/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1715/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (460/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (35/3 : ℝ) * a^1 * (c - b)^5 + (338/9 : ℝ) * (b - a)^6 + (1019/9 : ℝ) * (b - a)^5 * (c - b)^1 + (1456/9 : ℝ) * (b - a)^4 * (c - b)^2 + (138 : ℝ) * (b - a)^3 * (c - b)^3 + (179/3 : ℝ) * (b - a)^2 * (c - b)^4 + (70/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (35*a^5*b/9 + 70*a^5*c/9 + 28*a^4*b^2 + 131*a^4*b*c/9 + 187*a^4*c^2/9 - 206*a^3*b^3/9 - 55*a^3*b^2*c/3 + 545*a^3*b*c^2/9 - 206*a^3*c^3/9 + 187*a^2*b^4/9 + 545*a^2*b^3*c/9 - 283*a^2*b^2*c^2 - 55*a^2*b*c^3/3 + 28*a^2*c^4 + 70*a*b^5/9 + 131*a*b^4*c/9 - 55*a*b^3*c^2/3 + 545*a*b^2*c^3/9 + 131*a*b*c^4/9 + 35*a*c^5/9 + 35*b^5*c/9 + 28*b^4*c^2 - 206*b^3*c^3/9 + 187*b^2*c^4/9 + 70*b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (294 : ℝ) * a^4 * (c - a)^2 + (294 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (294 : ℝ) * a^4 * (b - c)^2 + (7286/9 : ℝ) * a^3 * (c - a)^3 + (3553/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (3323/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (3298/9 : ℝ) * a^3 * (b - c)^3 + (2359/3 : ℝ) * a^2 * (c - a)^4 + (4538/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (4468/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (763 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (365/3 : ℝ) * a^2 * (b - c)^4 + (925/3 : ℝ) * a^1 * (c - a)^5 + (2215/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (2420/3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (1505/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (445/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (35/3 : ℝ) * a^1 * (b - c)^5 + (338/9 : ℝ) * (c - a)^6 + (1009/9 : ℝ) * (c - a)^5 * (b - c)^1 + (159 : ℝ) * (c - a)^4 * (b - c)^2 + (128 : ℝ) * (c - a)^3 * (b - c)^3 + (427/9 : ℝ) * (c - a)^2 * (b - c)^4 + (35/9 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (35*a^5*b/9 + 70*a^5*c/9 + 28*a^4*b^2 + 131*a^4*b*c/9 + 187*a^4*c^2/9 - 206*a^3*b^3/9 - 55*a^3*b^2*c/3 + 545*a^3*b*c^2/9 - 206*a^3*c^3/9 + 187*a^2*b^4/9 + 545*a^2*b^3*c/9 - 283*a^2*b^2*c^2 - 55*a^2*b*c^3/3 + 28*a^2*c^4 + 70*a*b^5/9 + 131*a*b^4*c/9 - 55*a*b^3*c^2/3 + 545*a*b^2*c^3/9 + 131*a*b*c^4/9 + 35*a*c^5/9 + 35*b^5*c/9 + 28*b^4*c^2 - 206*b^3*c^3/9 + 187*b^2*c^4/9 + 70*b*c^5/9) := by
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
  have he : (-15*a^4*b*c - 15*a^4*c^2 - 75*a^3*b^3 - 93*a^3*b^2*c - 18*a^3*b*c^2 + 35*a^3*b - 75*a^3*c^3 + 70*a^3*c - 15*a^2*b^4 - 18*a^2*b^3*c - 381*a^2*b^2*c^2 + 182*a^2*b^2 - 93*a^2*b*c^3 + 56*a^2*b*c + 182*a^2*c^2 - 15*a*b^4*c - 93*a*b^3*c^2 + 70*a*b^3 - 18*a*b^2*c^3 + 56*a*b^2*c - 15*a*b*c^4 + 56*a*b*c^2 + 35*a*c^3 - 75*b^3*c^3 + 35*b^3*c - 15*b^2*c^4 + 182*b^2*c^2 + 70*b*c^3) = (35*a^5*b/9 + 70*a^5*c/9 + 28*a^4*b^2 + 131*a^4*b*c/9 + 187*a^4*c^2/9 - 206*a^3*b^3/9 - 55*a^3*b^2*c/3 + 545*a^3*b*c^2/9 - 206*a^3*c^3/9 + 187*a^2*b^4/9 + 545*a^2*b^3*c/9 - 283*a^2*b^2*c^2 - 55*a^2*b*c^3/3 + 28*a^2*c^4 + 70*a*b^5/9 + 131*a*b^4*c/9 - 55*a*b^3*c^2/3 + 545*a*b^2*c^3/9 + 131*a*b*c^4/9 + 35*a*c^5/9 + 35*b^5*c/9 + 28*b^4*c^2 - 206*b^3*c^3/9 + 187*b^2*c^4/9 + 70*b*c^5/9) := by
    linear_combination (-35*a^4*b/9 - 70*a^4*c/9 - 217*a^3*b^2/9 - 161*a^3*b*c/9 - 35*a^3*b/3 - 28*a^3*c^2 - 70*a^3*c/3 - 28*a^2*b^3 - 98*a^2*b^2*c/3 - 182*a^2*b^2/3 - 98*a^2*b*c^2/3 - 56*a^2*b*c/3 - 217*a^2*c^3/9 - 182*a^2*c^2/3 - 70*a*b^4/9 - 161*a*b^3*c/9 - 70*a*b^3/3 - 98*a*b^2*c^2/3 - 56*a*b^2*c/3 - 161*a*b*c^3/9 - 56*a*b*c^2/3 - 35*a*c^4/9 - 35*a*c^3/3 - 35*b^4*c/9 - 217*b^3*c^2/9 - 35*b^3*c/3 - 28*b^2*c^3 - 182*b^2*c^2/3 - 70*b*c^4/9 - 70*b*c^3/3) * habc
  have hn : 0 ≤ (-15*a^4*b*c - 15*a^4*c^2 - 75*a^3*b^3 - 93*a^3*b^2*c - 18*a^3*b*c^2 + 35*a^3*b - 75*a^3*c^3 + 70*a^3*c - 15*a^2*b^4 - 18*a^2*b^3*c - 381*a^2*b^2*c^2 + 182*a^2*b^2 - 93*a^2*b*c^3 + 56*a^2*b*c + 182*a^2*c^2 - 15*a*b^4*c - 93*a*b^3*c^2 + 70*a*b^3 - 18*a*b^2*c^3 + 56*a*b^2*c - 15*a*b*c^4 + 56*a*b*c^2 + 35*a*c^3 - 75*b^3*c^3 + 35*b^3*c - 15*b^2*c^4 + 182*b^2*c^2 + 70*b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (1 / (5 * a ^ 2 + a * b + b * c) + 1 / (5 * b ^ 2 + b * c + c * a) + 1 / (5 * c ^ 2 + c * a + a * b)) ≥ 3 / 7) := @solution
#print axioms solution
