-- Prove2me | solution 1 for WorkbookSource.base_35848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:08:58.131743+00:00
-- url     : https://prove2.me/submissions/46c5078f-92c8-4a11-b2b5-6d3cc07ed74d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 2 * ((12 * a ^ 2 + 12 * b ^ 2 - 3 * c ^ 2 + 3 * a * b + 9 * c * a + 9 * c * b) / (3 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2)) - 1 / (a + b + c) ^ 2) + (b - c) ^ 2 * ((12 * b ^ 2 + 12 * c ^ 2 - 3 * a ^ 2 + 3 * b * c + 9 * a * b + 9 * a * c) / (3 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) - 1 / (a + b + c) ^ 2) + (c - a) ^ 2 * ((12 * c ^ 2 + 12 * a ^ 2 - 3 * b ^ 2 + 3 * c * a + 9 * b * c + 9 * b * a) / (3 * (2 * c ^ 2 + (a + b) ^ 2) * (2 * a ^ 2 + (b + c) ^ 2)) - 1 / (a + b + c) ^ 2) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^8 + 16*a^7*b + 16*a^7*c + 7*a^6*b^2 + 42*a^6*b*c + 7*a^6*c^2 + 2*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 2*a^5*c^3 + 14*a^4*b^4 - 32*a^4*b^3*c - 56*a^4*b^2*c^2 - 32*a^4*b*c^3 + 14*a^4*c^4 + 2*a^3*b^5 - 32*a^3*b^4*c - 34*a^3*b^3*c^2 - 34*a^3*b^2*c^3 - 32*a^3*b*c^4 + 2*a^3*c^5 + 7*a^2*b^6 + 22*a^2*b^5*c - 56*a^2*b^4*c^2 - 34*a^2*b^3*c^3 - 56*a^2*b^2*c^4 + 22*a^2*b*c^5 + 7*a^2*c^6 + 16*a*b^7 + 42*a*b^6*c + 22*a*b^5*c^2 - 32*a*b^4*c^3 - 32*a*b^3*c^4 + 22*a*b^2*c^5 + 42*a*b*c^6 + 16*a*c^7 + 4*b^8 + 16*b^7*c + 7*b^6*c^2 + 2*b^5*c^3 + 14*b^4*c^4 + 2*b^3*c^5 + 7*b^2*c^6 + 16*b*c^7 + 4*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1080 : ℝ) * a^6 * (b - a)^2 + (1080 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1080 : ℝ) * a^6 * (c - b)^2 + (4032 : ℝ) * a^5 * (b - a)^3 + (6048 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (6912 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (2448 : ℝ) * a^5 * (c - b)^3 + (6348 : ℝ) * a^4 * (b - a)^4 + (12696 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (17244 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (10896 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2388 : ℝ) * a^4 * (c - b)^4 + (5392 : ℝ) * a^3 * (b - a)^5 + (13480 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (21616 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (18944 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (7976 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1280 : ℝ) * a^3 * (c - b)^5 + (2600 : ℝ) * a^2 * (b - a)^6 + (7800 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (14481 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (15962 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (9777 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3096 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (392 : ℝ) * a^2 * (c - b)^6 + (672 : ℝ) * a^1 * (b - a)^7 + (2352 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (4940 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (6470 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (5144 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (2422 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (616 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (64 : ℝ) * a^1 * (c - b)^7 + (72 : ℝ) * (b - a)^8 + (288 : ℝ) * (b - a)^7 * (c - b)^1 + (670 : ℝ) * (b - a)^6 * (c - b)^2 + (1002 : ℝ) * (b - a)^5 * (c - b)^3 + (969 : ℝ) * (b - a)^4 * (c - b)^4 + (604 : ℝ) * (b - a)^3 * (c - b)^5 + (231 : ℝ) * (b - a)^2 * (c - b)^6 + (48 : ℝ) * (b - a)^1 * (c - b)^7 + (4 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^8 + 16*a^7*b + 16*a^7*c + 7*a^6*b^2 + 42*a^6*b*c + 7*a^6*c^2 + 2*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 2*a^5*c^3 + 14*a^4*b^4 - 32*a^4*b^3*c - 56*a^4*b^2*c^2 - 32*a^4*b*c^3 + 14*a^4*c^4 + 2*a^3*b^5 - 32*a^3*b^4*c - 34*a^3*b^3*c^2 - 34*a^3*b^2*c^3 - 32*a^3*b*c^4 + 2*a^3*c^5 + 7*a^2*b^6 + 22*a^2*b^5*c - 56*a^2*b^4*c^2 - 34*a^2*b^3*c^3 - 56*a^2*b^2*c^4 + 22*a^2*b*c^5 + 7*a^2*c^6 + 16*a*b^7 + 42*a*b^6*c + 22*a*b^5*c^2 - 32*a*b^4*c^3 - 32*a*b^3*c^4 + 22*a*b^2*c^5 + 42*a*b*c^6 + 16*a*c^7 + 4*b^8 + 16*b^7*c + 7*b^6*c^2 + 2*b^5*c^3 + 14*b^4*c^4 + 2*b^3*c^5 + 7*b^2*c^6 + 16*b*c^7 + 4*c^8) := by
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
  have hn : 0 ≤ (4*a^8 + 16*a^7*b + 16*a^7*c + 7*a^6*b^2 + 42*a^6*b*c + 7*a^6*c^2 + 2*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 2*a^5*c^3 + 14*a^4*b^4 - 32*a^4*b^3*c - 56*a^4*b^2*c^2 - 32*a^4*b*c^3 + 14*a^4*c^4 + 2*a^3*b^5 - 32*a^3*b^4*c - 34*a^3*b^3*c^2 - 34*a^3*b^2*c^3 - 32*a^3*b*c^4 + 2*a^3*c^5 + 7*a^2*b^6 + 22*a^2*b^5*c - 56*a^2*b^4*c^2 - 34*a^2*b^3*c^3 - 56*a^2*b^2*c^4 + 22*a^2*b*c^5 + 7*a^2*c^6 + 16*a*b^7 + 42*a*b^6*c + 22*a*b^5*c^2 - 32*a*b^4*c^3 - 32*a*b^3*c^4 + 22*a*b^2*c^5 + 42*a*b*c^6 + 16*a*c^7 + 4*b^8 + 16*b^7*c + 7*b^6*c^2 + 2*b^5*c^3 + 14*b^4*c^4 + 2*b^3*c^5 + 7*b^2*c^6 + 16*b*c^7 + 4*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a - b) ^ 2 * ((12 * a ^ 2 + 12 * b ^ 2 - 3 * c ^ 2 + 3 * a * b + 9 * c * a + 9 * c * b) / (3 * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2)) - 1 / (a + b + c) ^ 2) + (b - c) ^ 2 * ((12 * b ^ 2 + 12 * c ^ 2 - 3 * a ^ 2 + 3 * b * c + 9 * a * b + 9 * a * c) / (3 * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2)) - 1 / (a + b + c) ^ 2) + (c - a) ^ 2 * ((12 * c ^ 2 + 12 * a ^ 2 - 3 * b ^ 2 + 3 * c * a + 9 * b * c + 9 * b * a) / (3 * (2 * c ^ 2 + (a + b) ^ 2) * (2 * a ^ 2 + (b + c) ^ 2)) - 1 / (a + b + c) ^ 2) ≥ 0) := @solution
#print axioms solution
