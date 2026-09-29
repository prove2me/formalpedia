-- Prove2me | solution 1 for WorkbookSource.base_46175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:55.856792+00:00
-- url     : https://prove2.me/submissions/de932836-f9e3-4d7e-87c5-827f1487d95c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b + b * c + c * a ≥ 4 * a ^ 3 * (b + c - a) / (b + c) ^ 2 + 4 * b ^ 3 * (c + a - b) / (c + a) ^ 2 + 4 * c ^ 3 * (a + b - c) / (a + b) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^8 + 4*a^7*b + 4*a^7*c - 4*a^6*b^2 - 4*a^6*c^2 - 3*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 - 3*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c + 2*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^5 + a^3*b^4*c + 14*a^3*b^3*c^2 + 14*a^3*b^2*c^3 + a^3*b*c^4 - 3*a^3*c^5 - 4*a^2*b^6 - 9*a^2*b^5*c + 2*a^2*b^4*c^2 + 14*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - 9*a^2*b*c^5 - 4*a^2*c^6 + 4*a*b^7 - 9*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 9*a*b^2*c^5 + 4*a*c^7 + 4*b^8 + 4*b^7*c - 4*b^6*c^2 - 3*b^5*c^3 + 2*b^4*c^4 - 3*b^3*c^5 - 4*b^2*c^6 + 4*b*c^7 + 4*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^6 * (b - a)^2 + (32 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^6 * (c - b)^2 + (32 : ℝ) * a^5 * (b - a)^3 + (48 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (336 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (160 : ℝ) * a^5 * (c - b)^3 + (8 : ℝ) * a^4 * (b - a)^4 + (16 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1064 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1056 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (328 : ℝ) * a^4 * (c - b)^4 + (32 : ℝ) * a^3 * (b - a)^5 + (80 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1696 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (2464 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1456 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (320 : ℝ) * a^3 * (c - b)^5 + (48 : ℝ) * a^2 * (b - a)^6 + (144 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1451 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2662 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (2267 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (960 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (160 : ℝ) * a^2 * (c - b)^6 + (24 : ℝ) * a^1 * (b - a)^7 + (84 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (624 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1350 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1484 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (918 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (300 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (40 : ℝ) * a^1 * (c - b)^7 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (105 : ℝ) * (b - a)^6 * (c - b)^2 + (259 : ℝ) * (b - a)^5 * (c - b)^3 + (347 : ℝ) * (b - a)^4 * (c - b)^4 + (281 : ℝ) * (b - a)^3 * (c - b)^5 + (136 : ℝ) * (b - a)^2 * (c - b)^6 + (36 : ℝ) * (b - a)^1 * (c - b)^7 + (4 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^8 + 4*a^7*b + 4*a^7*c - 4*a^6*b^2 - 4*a^6*c^2 - 3*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 - 3*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c + 2*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^5 + a^3*b^4*c + 14*a^3*b^3*c^2 + 14*a^3*b^2*c^3 + a^3*b*c^4 - 3*a^3*c^5 - 4*a^2*b^6 - 9*a^2*b^5*c + 2*a^2*b^4*c^2 + 14*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - 9*a^2*b*c^5 - 4*a^2*c^6 + 4*a*b^7 - 9*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 9*a*b^2*c^5 + 4*a*c^7 + 4*b^8 + 4*b^7*c - 4*b^6*c^2 - 3*b^5*c^3 + 2*b^4*c^4 - 3*b^3*c^5 - 4*b^2*c^6 + 4*b*c^7 + 4*c^8) := by
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
  have hn : 0 ≤ (4*a^8 + 4*a^7*b + 4*a^7*c - 4*a^6*b^2 - 4*a^6*c^2 - 3*a^5*b^3 - 9*a^5*b^2*c - 9*a^5*b*c^2 - 3*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c + 2*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 - 3*a^3*b^5 + a^3*b^4*c + 14*a^3*b^3*c^2 + 14*a^3*b^2*c^3 + a^3*b*c^4 - 3*a^3*c^5 - 4*a^2*b^6 - 9*a^2*b^5*c + 2*a^2*b^4*c^2 + 14*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - 9*a^2*b*c^5 - 4*a^2*c^6 + 4*a*b^7 - 9*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 - 9*a*b^2*c^5 + 4*a*c^7 + 4*b^8 + 4*b^7*c - 4*b^6*c^2 - 3*b^5*c^3 + 2*b^4*c^4 - 3*b^3*c^5 - 4*b^2*c^6 + 4*b*c^7 + 4*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b + b * c + c * a ≥ 4 * a ^ 3 * (b + c - a) / (b + c) ^ 2 + 4 * b ^ 3 * (c + a - b) / (c + a) ^ 2 + 4 * c ^ 3 * (a + b - c) / (a + b) ^ 2) := @solution
#print axioms solution
