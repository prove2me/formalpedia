-- Prove2me | solution 1 for WorkbookSource.base_47025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:31.139994+00:00
-- url     : https://prove2.me/submissions/120a534f-cdf4-4470-bf77-f5221dbb830a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 / (2 * a + b) + 4 / (2 * b + c) + 3 / (2 * c + a)) ≥ (12 / (3 * a + 2 * b + c) + 8 / (a + 3 * b + 2 * c) + 4 / (2 * a + b + 3 * c))  := by
  have hp : 0 ≤ (48*a^5 + 20*a^4*b + 178*a^4*c - 34*a^3*b^2 - 33*a^3*b*c + 145*a^3*c^2 + 124*a^2*b^3 - 270*a^2*b^2*c - 297*a^2*b*c^2 - 55*a^2*c^3 + 142*a*b^4 - 3*a*b^3*c - 297*a*b^2*c^2 - 108*a*b*c^3 - 4*a*c^4 + 36*b^5 + 32*b^4*c - 43*b^3*c^2 + 151*b^2*c^3 + 208*b*c^4 + 60*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (1404 : ℝ) * a^3 * (b - a)^2 + (1512 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1296 : ℝ) * a^3 * (c - b)^2 + (2862 : ℝ) * a^2 * (b - a)^3 + (5346 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (5022 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (1404 : ℝ) * a^2 * (c - b)^3 + (1950 : ℝ) * a^1 * (b - a)^4 + (5187 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (6129 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (3042 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (504 : ℝ) * a^1 * (c - b)^4 + (444 : ℝ) * (b - a)^5 + (1531 : ℝ) * (b - a)^4 * (c - b)^1 + (2258 : ℝ) * (b - a)^3 * (c - b)^2 + (1583 : ℝ) * (b - a)^2 * (c - b)^3 + (508 : ℝ) * (b - a)^1 * (c - b)^4 + (60 : ℝ) * (c - b)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (1404 : ℝ) * a^3 * (c - a)^2 + (1296 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (1188 : ℝ) * a^3 * (b - c)^2 + (2862 : ℝ) * a^2 * (c - a)^3 + (3240 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (2916 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (1134 : ℝ) * a^2 * (b - c)^3 + (1950 : ℝ) * a^1 * (c - a)^4 + (2613 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (2268 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (1455 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (354 : ℝ) * a^1 * (b - c)^4 + (444 : ℝ) * (c - a)^5 + (689 : ℝ) * (c - a)^4 * (b - c)^1 + (574 : ℝ) * (c - a)^3 * (b - c)^2 + (445 : ℝ) * (c - a)^2 * (b - c)^3 + (212 : ℝ) * (c - a)^1 * (b - c)^4 + (36 : ℝ) * (b - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (1296 : ℝ) * c^3 * (a - c)^2 + (1080 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (1188 : ℝ) * c^3 * (b - a)^2 + (2484 : ℝ) * c^2 * (a - c)^3 + (4050 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (4050 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (1134 : ℝ) * c^2 * (b - a)^3 + (1584 : ℝ) * c^1 * (a - c)^4 + (3834 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (4563 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (2229 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (354 : ℝ) * c^1 * (b - a)^4 + (336 : ℝ) * (a - c)^5 + (1072 : ℝ) * (a - c)^4 * (b - a)^1 + (1550 : ℝ) * (a - c)^3 * (b - a)^2 + (1052 : ℝ) * (a - c)^2 * (b - a)^3 + (322 : ℝ) * (a - c)^1 * (b - a)^4 + (36 : ℝ) * (b - a)^5 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (1188 : ℝ) * b^3 * (a - b)^2 + (1080 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (1296 : ℝ) * b^3 * (c - a)^2 + (2430 : ℝ) * b^2 * (a - b)^3 + (2754 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (3078 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (1404 : ℝ) * b^2 * (c - a)^3 + (1650 : ℝ) * b^1 * (a - b)^4 + (2229 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (2295 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (1782 : ℝ) * b^1 * (a - b)^1 * (c - a)^3 + (504 : ℝ) * b^1 * (c - a)^4 + (372 : ℝ) * (a - b)^5 + (587 : ℝ) * (a - b)^4 * (c - a)^1 + (556 : ℝ) * (a - b)^3 * (c - a)^2 + (529 : ℝ) * (a - b)^2 * (c - a)^3 + (296 : ℝ) * (a - b)^1 * (c - a)^4 + (60 : ℝ) * (c - a)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (1188 : ℝ) * b^3 * (c - b)^2 + (1296 : ℝ) * b^3 * (c - b)^1 * (a - c)^1 + (1404 : ℝ) * b^3 * (a - c)^2 + (2430 : ℝ) * b^2 * (c - b)^3 + (4536 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (4860 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (1350 : ℝ) * b^2 * (a - c)^3 + (1650 : ℝ) * b^1 * (c - b)^4 + (4371 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (5508 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (2721 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (438 : ℝ) * b^1 * (a - c)^4 + (372 : ℝ) * (c - b)^5 + (1273 : ℝ) * (c - b)^4 * (a - c)^1 + (1928 : ℝ) * (c - b)^3 * (a - c)^2 + (1337 : ℝ) * (c - b)^2 * (a - c)^3 + (418 : ℝ) * (c - b)^1 * (a - c)^4 + (48 : ℝ) * (a - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (1296 : ℝ) * c^3 * (b - c)^2 + (1512 : ℝ) * c^3 * (b - c)^1 * (a - b)^1 + (1404 : ℝ) * c^3 * (a - b)^2 + (2484 : ℝ) * c^2 * (b - c)^3 + (3402 : ℝ) * c^2 * (b - c)^2 * (a - b)^1 + (3402 : ℝ) * c^2 * (b - c)^1 * (a - b)^2 + (1350 : ℝ) * c^2 * (a - b)^3 + (1584 : ℝ) * c^1 * (b - c)^4 + (2502 : ℝ) * c^1 * (b - c)^3 * (a - b)^1 + (2565 : ℝ) * c^1 * (b - c)^2 * (a - b)^2 + (1731 : ℝ) * c^1 * (b - c)^1 * (a - b)^3 + (438 : ℝ) * c^1 * (a - b)^4 + (336 : ℝ) * (b - c)^5 + (608 : ℝ) * (b - c)^4 * (a - b)^1 + (622 : ℝ) * (b - c)^3 * (a - b)^2 + (526 : ℝ) * (b - c)^2 * (a - b)^3 + (260 : ℝ) * (b - c)^1 * (a - b)^4 + (48 : ℝ) * (a - b)^5 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (48*a^5 + 20*a^4*b + 178*a^4*c - 34*a^3*b^2 - 33*a^3*b*c + 145*a^3*c^2 + 124*a^2*b^3 - 270*a^2*b^2*c - 297*a^2*b*c^2 - 55*a^2*c^3 + 142*a*b^4 - 3*a*b^3*c - 297*a*b^2*c^2 - 108*a*b*c^3 - 4*a*c^4 + 36*b^5 + 32*b^4*c - 43*b^3*c^2 + 151*b^2*c^3 + 208*b*c^4 + 60*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (5 / (2 * a + b) + 4 / (2 * b + c) + 3 / (2 * c + a)) ≥ (12 / (3 * a + 2 * b + c) + 8 / (a + 3 * b + 2 * c) + 4 / (2 * a + b + 3 * c))) := @solution
#print axioms solution
