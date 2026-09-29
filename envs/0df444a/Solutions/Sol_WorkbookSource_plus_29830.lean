-- Prove2me | solution 1 for WorkbookSource.plus_29830
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:35:39.621463+00:00
-- url     : https://prove2.me/submissions/0a19ed66-4b09-4d56-b44a-5b79d8746ea2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a ^ 2 + b ^ 2 + 25) + 1 / (b ^ 2 + c ^ 2 + 25) + 1 / (c ^ 2 + a ^ 2 + 25) ≤ 1 / 9   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3196*a^6/729 + 2564*a^5*b/243 + 2564*a^5*c/243 + 3071*a^4*b^2/243 + 964*a^4*b*c/243 + 3071*a^4*c^2/243 + 7976*a^3*b^3/729 - 5608*a^3*b^2*c/243 - 5608*a^3*b*c^2/243 + 7976*a^3*c^3/729 + 3071*a^2*b^4/243 - 5608*a^2*b^3*c/243 - 4742*a^2*b^2*c^2/81 - 5608*a^2*b*c^3/243 + 3071*a^2*c^4/243 + 2564*a*b^5/243 + 964*a*b^4*c/243 - 5608*a*b^3*c^2/243 - 5608*a*b^2*c^3/243 + 964*a*b*c^4/243 + 2564*a*c^5/243 + 3196*b^6/729 + 2564*b^5*c/243 + 3071*b^4*c^2/243 + 7976*b^3*c^3/729 + 3071*b^2*c^4/243 + 2564*b*c^5/243 + 3196*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (300 : ℝ) * a^4 * (b - a)^2 + (300 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (300 : ℝ) * a^4 * (c - b)^2 + (21832/27 : ℝ) * a^3 * (b - a)^3 + (10916/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (10684/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (10568/27 : ℝ) * a^3 * (c - b)^3 + (22310/27 : ℝ) * a^2 * (b - a)^4 + (44620/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (16330/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (26680/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (5414/27 : ℝ) * a^2 * (c - b)^4 + (10244/27 : ℝ) * a^1 * (b - a)^5 + (25610/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (32596/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (23284/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8614/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1280/27 : ℝ) * a^1 * (c - b)^5 + (48178/729 : ℝ) * (b - a)^6 + (48178/243 : ℝ) * (b - a)^5 * (c - b)^1 + (71093/243 : ℝ) * (b - a)^4 * (c - b)^2 + (185668/729 : ℝ) * (b - a)^3 * (c - b)^3 + (31871/243 : ℝ) * (b - a)^2 * (c - b)^4 + (8956/243 : ℝ) * (b - a)^1 * (c - b)^5 + (3196/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3196*a^6/729 + 2564*a^5*b/243 + 2564*a^5*c/243 + 3071*a^4*b^2/243 + 964*a^4*b*c/243 + 3071*a^4*c^2/243 + 7976*a^3*b^3/729 - 5608*a^3*b^2*c/243 - 5608*a^3*b*c^2/243 + 7976*a^3*c^3/729 + 3071*a^2*b^4/243 - 5608*a^2*b^3*c/243 - 4742*a^2*b^2*c^2/81 - 5608*a^2*b*c^3/243 + 3071*a^2*c^4/243 + 2564*a*b^5/243 + 964*a*b^4*c/243 - 5608*a*b^3*c^2/243 - 5608*a*b^2*c^3/243 + 964*a*b*c^4/243 + 2564*a*c^5/243 + 3196*b^6/729 + 2564*b^5*c/243 + 3071*b^4*c^2/243 + 7976*b^3*c^3/729 + 3071*b^2*c^4/243 + 2564*b*c^5/243 + 3196*c^6/729) := by
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
  have he : (a^4*b^2 + a^4*c^2 + 16*a^4 + a^2*b^4 + 2*a^2*b^2*c^2 + 48*a^2*b^2 + a^2*c^4 + 48*a^2*c^2 + 350*a^2 + b^4*c^2 + 16*b^4 + b^2*c^4 + 48*b^2*c^2 + 350*b^2 + 16*c^4 + 350*c^2 - 1250) = (3196*a^6/729 + 2564*a^5*b/243 + 2564*a^5*c/243 + 3071*a^4*b^2/243 + 964*a^4*b*c/243 + 3071*a^4*c^2/243 + 7976*a^3*b^3/729 - 5608*a^3*b^2*c/243 - 5608*a^3*b*c^2/243 + 7976*a^3*c^3/729 + 3071*a^2*b^4/243 - 5608*a^2*b^3*c/243 - 4742*a^2*b^2*c^2/81 - 5608*a^2*b*c^3/243 + 3071*a^2*c^4/243 + 2564*a*b^5/243 + 964*a*b^4*c/243 - 5608*a*b^3*c^2/243 - 5608*a*b^2*c^3/243 + 964*a*b*c^4/243 + 2564*a*c^5/243 + 3196*b^6/729 + 2564*b^5*c/243 + 3071*b^4*c^2/243 + 7976*b^3*c^3/729 + 3071*b^2*c^4/243 + 2564*b*c^5/243 + 3196*c^6/729) := by
    linear_combination (-3196*a^5/729 - 4496*a^4*b/729 - 4496*a^4*c/729 - 3196*a^4/243 - 3988*a^3*b^2/729 + 6100*a^3*b*c/729 - 1300*a^3*b/243 - 3988*a^3*c^2/729 - 1300*a^3*c/243 - 1900*a^3/81 - 3988*a^2*b^3/729 + 4904*a^2*b^2*c/243 - 896*a^2*b^2/81 + 4904*a^2*b*c^2/243 + 2900*a^2*b*c/81 + 200*a^2*b/27 - 3988*a^2*c^3/729 - 896*a^2*c^2/81 + 200*a^2*c/27 - 1900*a^2/27 - 4496*a*b^4/729 + 6100*a*b^3*c/729 - 1300*a*b^3/243 + 4904*a*b^2*c^2/243 + 2900*a*b^2*c/81 + 200*a*b^2/27 + 6100*a*b*c^3/729 + 2900*a*b*c^2/81 + 2500*a*b*c/27 + 2500*a*b/27 - 4496*a*c^4/729 - 1300*a*c^3/243 + 200*a*c^2/27 + 2500*a*c/27 + 1250*a/9 - 3196*b^5/729 - 4496*b^4*c/729 - 3196*b^4/243 - 3988*b^3*c^2/729 - 1300*b^3*c/243 - 1900*b^3/81 - 3988*b^2*c^3/729 - 896*b^2*c^2/81 + 200*b^2*c/27 - 1900*b^2/27 - 4496*b*c^4/729 - 1300*b*c^3/243 + 200*b*c^2/27 + 2500*b*c/27 + 1250*b/9 - 3196*c^5/729 - 3196*c^4/243 - 1900*c^3/81 - 1900*c^2/27 + 1250*c/9 + 1250/3) * habc
  have hn : 0 ≤ (a^4*b^2 + a^4*c^2 + 16*a^4 + a^2*b^4 + 2*a^2*b^2*c^2 + 48*a^2*b^2 + a^2*c^4 + 48*a^2*c^2 + 350*a^2 + b^4*c^2 + 16*b^4 + b^2*c^4 + 48*b^2*c^2 + 350*b^2 + 16*c^4 + 350*c^2 - 1250) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (a ^ 2 + b ^ 2 + 25) + 1 / (b ^ 2 + c ^ 2 + 25) + 1 / (c ^ 2 + a ^ 2 + 25) ≤ 1 / 9) := @solution
#print axioms solution
