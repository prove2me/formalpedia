-- Prove2me | solution 1 for WorkbookSource.base_5208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:37.174693+00:00
-- url     : https://prove2.me/submissions/e6276ffa-238a-4ec0-bb05-d9d1d5600344

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a / (b ^ 2 + c ^ 2 + 9) + b / (c ^ 2 + a ^ 2 + 9) + c / (a ^ 2 + b ^ 2 + 9)) ≤ (1 / 11) * (1 / a + 1 / b + 1 / c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^7*b + 4*a^7*c + 16*a^6*b^2 - 8*a^6*b*c + 16*a^6*c^2 + 34*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 34*a^5*c^3 + 42*a^4*b^4 - 2*a^4*b^3*c - 56*a^4*b^2*c^2 - 2*a^4*b*c^3 + 42*a^4*c^4 + 34*a^3*b^5 - 2*a^3*b^4*c - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 - 2*a^3*b*c^4 + 34*a^3*c^5 + 16*a^2*b^6 - 4*a^2*b^5*c - 56*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 56*a^2*b^2*c^4 - 4*a^2*b*c^5 + 16*a^2*c^6 + 4*a*b^7 - 8*a*b^6*c - 4*a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 - 8*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 16*b^6*c^2 + 34*b^5*c^3 + 42*b^4*c^4 + 34*b^3*c^5 + 16*b^2*c^6 + 4*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (858 : ℝ) * a^6 * (b - a)^2 + (858 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (858 : ℝ) * a^6 * (c - b)^2 + (3776 : ℝ) * a^5 * (b - a)^3 + (5664 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (4632 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1372 : ℝ) * a^5 * (c - b)^3 + (6974 : ℝ) * a^4 * (b - a)^4 + (13948 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (12332 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (5358 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (964 : ℝ) * a^4 * (c - b)^4 + (6924 : ℝ) * a^3 * (b - a)^5 + (17310 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (18076 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (9804 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2858 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (372 : ℝ) * a^3 * (c - b)^5 + (3898 : ℝ) * a^2 * (b - a)^6 + (11694 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (14606 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (9722 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (3710 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (798 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (80 : ℝ) * a^2 * (c - b)^6 + (1180 : ℝ) * a^1 * (b - a)^7 + (4130 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (6106 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (4940 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (2366 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (674 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (108 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (150 : ℝ) * (b - a)^8 + (600 : ℝ) * (b - a)^7 * (c - b)^1 + (1034 : ℝ) * (b - a)^6 * (c - b)^2 + (1002 : ℝ) * (b - a)^5 * (c - b)^3 + (592 : ℝ) * (b - a)^4 * (c - b)^4 + (214 : ℝ) * (b - a)^3 * (c - b)^5 + (44 : ℝ) * (b - a)^2 * (c - b)^6 + (4 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^7*b + 4*a^7*c + 16*a^6*b^2 - 8*a^6*b*c + 16*a^6*c^2 + 34*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 34*a^5*c^3 + 42*a^4*b^4 - 2*a^4*b^3*c - 56*a^4*b^2*c^2 - 2*a^4*b*c^3 + 42*a^4*c^4 + 34*a^3*b^5 - 2*a^3*b^4*c - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 - 2*a^3*b*c^4 + 34*a^3*c^5 + 16*a^2*b^6 - 4*a^2*b^5*c - 56*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 56*a^2*b^2*c^4 - 4*a^2*b*c^5 + 16*a^2*c^6 + 4*a*b^7 - 8*a*b^6*c - 4*a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 - 8*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 16*b^6*c^2 + 34*b^5*c^3 + 42*b^4*c^4 + 34*b^3*c^5 + 16*b^2*c^6 + 4*b*c^7) := by
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
  have he : (-11*a^6*b*c + a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 9*a^5*b + a^5*c^3 + 9*a^5*c - 10*a^4*b^3*c - 10*a^4*b*c^3 - 189*a^4*b*c + a^3*b^5 - 10*a^3*b^4*c - 9*a^3*b^3*c^2 + 27*a^3*b^3 - 9*a^3*b^2*c^3 - 72*a^3*b^2*c - 10*a^3*b*c^4 - 72*a^3*b*c^2 + 162*a^3*b + a^3*c^5 + 27*a^3*c^3 + 162*a^3*c + a^2*b^5*c - 9*a^2*b^3*c^3 - 72*a^2*b^3*c + a^2*b*c^5 - 72*a^2*b*c^3 - 729*a^2*b*c - 11*a*b^6*c + a*b^5*c^2 + 9*a*b^5 - 10*a*b^4*c^3 - 189*a*b^4*c - 10*a*b^3*c^4 - 72*a*b^3*c^2 + 162*a*b^3 + a*b^2*c^5 - 72*a*b^2*c^3 - 729*a*b^2*c - 11*a*b*c^6 - 189*a*b*c^4 - 729*a*b*c^2 + 729*a*b + 9*a*c^5 + 162*a*c^3 + 729*a*c + b^5*c^3 + 9*b^5*c + b^3*c^5 + 27*b^3*c^3 + 162*b^3*c + 9*b*c^5 + 162*b*c^3 + 729*b*c) = (4*a^7*b + 4*a^7*c + 16*a^6*b^2 - 8*a^6*b*c + 16*a^6*c^2 + 34*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 34*a^5*c^3 + 42*a^4*b^4 - 2*a^4*b^3*c - 56*a^4*b^2*c^2 - 2*a^4*b*c^3 + 42*a^4*c^4 + 34*a^3*b^5 - 2*a^3*b^4*c - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 - 2*a^3*b*c^4 + 34*a^3*c^5 + 16*a^2*b^6 - 4*a^2*b^5*c - 56*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 56*a^2*b^2*c^4 - 4*a^2*b*c^5 + 16*a^2*c^6 + 4*a*b^7 - 8*a*b^6*c - 4*a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - 4*a*b^2*c^5 - 8*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 16*b^6*c^2 + 34*b^5*c^3 + 42*b^4*c^4 + 34*b^3*c^5 + 16*b^2*c^6 + 4*b*c^7) := by
    linear_combination (-4*a^6*b - 4*a^6*c - 12*a^5*b^2 + 5*a^5*b*c - 12*a^5*b - 12*a^5*c^2 - 12*a^5*c - 21*a^4*b^3 + 12*a^4*b^2*c - 24*a^4*b^2 + 12*a^4*b*c^2 + 39*a^4*b*c - 27*a^4*b - 21*a^4*c^3 - 24*a^4*c^2 - 27*a^4*c - 21*a^3*b^4 + a^3*b^3*c - 39*a^3*b^3 + 32*a^3*b^2*c^2 + 21*a^3*b^2*c - 45*a^3*b^2 + a^3*b*c^3 + 21*a^3*b*c^2 - 18*a^3*b*c - 81*a^3*b - 21*a^3*c^4 - 39*a^3*c^3 - 45*a^3*c^2 - 81*a^3*c - 12*a^2*b^5 + 12*a^2*b^4*c - 24*a^2*b^4 + 32*a^2*b^3*c^2 + 21*a^2*b^3*c - 45*a^2*b^3 + 32*a^2*b^2*c^3 + 54*a^2*b^2*c^2 + 54*a^2*b^2*c - 54*a^2*b^2 + 12*a^2*b*c^4 + 21*a^2*b*c^3 + 54*a^2*b*c^2 + 108*a^2*b*c - 81*a^2*b - 12*a^2*c^5 - 24*a^2*c^4 - 45*a^2*c^3 - 54*a^2*c^2 - 81*a^2*c - 4*a*b^6 + 5*a*b^5*c - 12*a*b^5 + 12*a*b^4*c^2 + 39*a*b^4*c - 27*a*b^4 + a*b^3*c^3 + 21*a*b^3*c^2 - 18*a*b^3*c - 81*a*b^3 + 12*a*b^2*c^4 + 21*a*b^2*c^3 + 54*a*b^2*c^2 + 108*a*b^2*c - 81*a*b^2 + 5*a*b*c^5 + 39*a*b*c^4 - 18*a*b*c^3 + 108*a*b*c^2 - 243*a*b*c - 243*a*b - 4*a*c^6 - 12*a*c^5 - 27*a*c^4 - 81*a*c^3 - 81*a*c^2 - 243*a*c - 4*b^6*c - 12*b^5*c^2 - 12*b^5*c - 21*b^4*c^3 - 24*b^4*c^2 - 27*b^4*c - 21*b^3*c^4 - 39*b^3*c^3 - 45*b^3*c^2 - 81*b^3*c - 12*b^2*c^5 - 24*b^2*c^4 - 45*b^2*c^3 - 54*b^2*c^2 - 81*b^2*c - 4*b*c^6 - 12*b*c^5 - 27*b*c^4 - 81*b*c^3 - 81*b*c^2 - 243*b*c) * habc
  have hn : 0 ≤ (-11*a^6*b*c + a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 9*a^5*b + a^5*c^3 + 9*a^5*c - 10*a^4*b^3*c - 10*a^4*b*c^3 - 189*a^4*b*c + a^3*b^5 - 10*a^3*b^4*c - 9*a^3*b^3*c^2 + 27*a^3*b^3 - 9*a^3*b^2*c^3 - 72*a^3*b^2*c - 10*a^3*b*c^4 - 72*a^3*b*c^2 + 162*a^3*b + a^3*c^5 + 27*a^3*c^3 + 162*a^3*c + a^2*b^5*c - 9*a^2*b^3*c^3 - 72*a^2*b^3*c + a^2*b*c^5 - 72*a^2*b*c^3 - 729*a^2*b*c - 11*a*b^6*c + a*b^5*c^2 + 9*a*b^5 - 10*a*b^4*c^3 - 189*a*b^4*c - 10*a*b^3*c^4 - 72*a*b^3*c^2 + 162*a*b^3 + a*b^2*c^5 - 72*a*b^2*c^3 - 729*a*b^2*c - 11*a*b*c^6 - 189*a*b*c^4 - 729*a*b*c^2 + 729*a*b + 9*a*c^5 + 162*a*c^3 + 729*a*c + b^5*c^3 + 9*b^5*c + b^3*c^5 + 27*b^3*c^3 + 162*b^3*c + 9*b*c^5 + 162*b*c^3 + 729*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a / (b ^ 2 + c ^ 2 + 9) + b / (c ^ 2 + a ^ 2 + 9) + c / (a ^ 2 + b ^ 2 + 9)) ≤ (1 / 11) * (1 / a + 1 / b + 1 / c)) := @solution
#print axioms solution
