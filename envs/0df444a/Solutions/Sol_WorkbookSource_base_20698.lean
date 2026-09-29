-- Prove2me | solution 1 for WorkbookSource.base_20698
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:46:41.47013+00:00
-- url     : https://prove2.me/submissions/0f8ae4ed-805c-4d23-81bb-a1f0530f7d39

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (3 * a + 1) / (3 * b ^ 2 + 1) + (3 * b + 1) / (3 * c ^ 2 + 1) + (3 * c + 1) / (3 * a ^ 2 + 1) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (25*a^6/81 + 34*a^5*b/27 + 25*a^5*c/27 - 2*a^4*b^2/27 + 79*a^4*b*c/27 + 223*a^4*c^2/27 + 536*a^3*b^3/81 - 14*a^3*b^2*c/27 + 220*a^3*b*c^2/27 + 536*a^3*c^3/81 + 223*a^2*b^4/27 + 220*a^2*b^3*c/27 - 752*a^2*b^2*c^2/9 - 14*a^2*b*c^3/27 - 2*a^2*c^4/27 + 25*a*b^5/27 + 79*a*b^4*c/27 - 14*a*b^3*c^2/27 + 220*a*b^2*c^3/27 + 79*a*b*c^4/27 + 34*a*c^5/27 + 25*b^6/81 + 34*b^5*c/27 - 2*b^4*c^2/27 + 536*b^3*c^3/81 + 223*b^2*c^4/27 + 25*b*c^5/27 + 25*c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (88 : ℝ) * a^4 * (b - a)^2 + (88 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (88 : ℝ) * a^4 * (c - b)^2 + (776/3 : ℝ) * a^3 * (b - a)^3 + (424 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (352 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (280/3 : ℝ) * a^3 * (c - b)^3 + (824/3 : ℝ) * a^2 * (b - a)^4 + (1864/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (576 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (688/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (80/3 : ℝ) * a^2 * (c - b)^4 + (3275/27 : ℝ) * a^1 * (b - a)^5 + (9362/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (10448/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (5338/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1195/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (109/27 : ℝ) * a^1 * (c - b)^5 + (1426/81 : ℝ) * (b - a)^6 + (1633/27 : ℝ) * (b - a)^5 * (c - b)^1 + (749/9 : ℝ) * (b - a)^4 * (c - b)^2 + (4462/81 : ℝ) * (b - a)^3 * (c - b)^3 + (473/27 : ℝ) * (b - a)^2 * (c - b)^4 + (25/9 : ℝ) * (b - a)^1 * (c - b)^5 + (25/81 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (25*a^6/81 + 34*a^5*b/27 + 25*a^5*c/27 - 2*a^4*b^2/27 + 79*a^4*b*c/27 + 223*a^4*c^2/27 + 536*a^3*b^3/81 - 14*a^3*b^2*c/27 + 220*a^3*b*c^2/27 + 536*a^3*c^3/81 + 223*a^2*b^4/27 + 220*a^2*b^3*c/27 - 752*a^2*b^2*c^2/9 - 14*a^2*b*c^3/27 - 2*a^2*c^4/27 + 25*a*b^5/27 + 79*a*b^4*c/27 - 14*a*b^3*c^2/27 + 220*a*b^2*c^3/27 + 79*a*b*c^4/27 + 34*a*c^5/27 + 25*b^6/81 + 34*b^5*c/27 - 2*b^4*c^2/27 + 536*b^3*c^3/81 + 223*b^2*c^4/27 + 25*b*c^5/27 + 25*c^6/81) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (88 : ℝ) * a^4 * (c - a)^2 + (88 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (88 : ℝ) * a^4 * (b - c)^2 + (776/3 : ℝ) * a^3 * (c - a)^3 + (352 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (280 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (280/3 : ℝ) * a^3 * (b - c)^3 + (824/3 : ℝ) * a^2 * (c - a)^4 + (1432/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (360 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (472/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (80/3 : ℝ) * a^2 * (b - c)^4 + (3275/27 : ℝ) * a^1 * (c - a)^5 + (7013/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (5750/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (2584/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (790/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (109/27 : ℝ) * a^1 * (b - c)^5 + (1426/81 : ℝ) * (c - a)^6 + (1219/27 : ℝ) * (c - a)^5 * (b - c)^1 + (404/9 : ℝ) * (c - a)^4 * (b - c)^2 + (2032/81 : ℝ) * (c - a)^3 * (b - c)^3 + (293/27 : ℝ) * (c - a)^2 * (b - c)^4 + (28/9 : ℝ) * (c - a)^1 * (b - c)^5 + (25/81 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (25*a^6/81 + 34*a^5*b/27 + 25*a^5*c/27 - 2*a^4*b^2/27 + 79*a^4*b*c/27 + 223*a^4*c^2/27 + 536*a^3*b^3/81 - 14*a^3*b^2*c/27 + 220*a^3*b*c^2/27 + 536*a^3*c^3/81 + 223*a^2*b^4/27 + 220*a^2*b^3*c/27 - 752*a^2*b^2*c^2/9 - 14*a^2*b*c^3/27 - 2*a^2*c^4/27 + 25*a*b^5/27 + 79*a*b^4*c/27 - 14*a*b^3*c^2/27 + 220*a*b^2*c^3/27 + 79*a*b*c^4/27 + 34*a*c^5/27 + 25*b^6/81 + 34*b^5*c/27 - 2*b^4*c^2/27 + 536*b^3*c^3/81 + 223*b^2*c^4/27 + 25*b*c^5/27 + 25*c^6/81) := by
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
  have he : (27*a^3*c^2 + 9*a^3 + 27*a^2*b^3 - 81*a^2*b^2*c^2 - 18*a^2*b^2 + 9*a^2*b - 18*a^2*c^2 - 3*a^2 + 9*a*c^2 + 3*a + 9*b^3 + 27*b^2*c^3 - 18*b^2*c^2 + 9*b^2*c - 3*b^2 + 3*b + 9*c^3 - 3*c^2 + 3*c) = (25*a^6/81 + 34*a^5*b/27 + 25*a^5*c/27 - 2*a^4*b^2/27 + 79*a^4*b*c/27 + 223*a^4*c^2/27 + 536*a^3*b^3/81 - 14*a^3*b^2*c/27 + 220*a^3*b*c^2/27 + 536*a^3*c^3/81 + 223*a^2*b^4/27 + 220*a^2*b^3*c/27 - 752*a^2*b^2*c^2/9 - 14*a^2*b*c^3/27 - 2*a^2*c^4/27 + 25*a*b^5/27 + 79*a*b^4*c/27 - 14*a*b^3*c^2/27 + 220*a*b^2*c^3/27 + 79*a*b*c^4/27 + 34*a*c^5/27 + 25*b^6/81 + 34*b^5*c/27 - 2*b^4*c^2/27 + 536*b^3*c^3/81 + 223*b^2*c^4/27 + 25*b*c^5/27 + 25*c^6/81) := by
    linear_combination (-25*a^5/81 - 77*a^4*b/81 - 50*a^4*c/81 - 25*a^4/27 + 83*a^3*b^2/81 - 110*a^3*b*c/81 - 52*a^3*b/27 - 619*a^3*c^2/81 - 25*a^3*c/27 - 25*a^3/9 - 619*a^2*b^3/81 + 23*a^2*b^2*c/27 + 5*a^2*b^2 + 23*a^2*b*c^2/27 - 11*a^2*b*c/9 - 3*a^2*b + 83*a^2*c^3/81 + 5*a^2*c^2 + 2*a^2/3 - 50*a*b^4/81 - 110*a*b^3*c/81 - 25*a*b^3/27 + 23*a*b^2*c^2/27 - 11*a*b^2*c/9 - 110*a*b*c^3/81 - 11*a*b*c^2/9 - 2*a*b*c/3 - 2*a*b/3 - 77*a*c^4/81 - 52*a*c^3/27 - 3*a*c^2 - 2*a*c/3 - a - 25*b^5/81 - 77*b^4*c/81 - 25*b^4/27 + 83*b^3*c^2/81 - 52*b^3*c/27 - 25*b^3/9 - 619*b^2*c^3/81 + 5*b^2*c^2 - 3*b^2*c + 2*b^2/3 - 50*b*c^4/81 - 25*b*c^3/27 - 2*b*c/3 - b - 25*c^5/81 - 25*c^4/27 - 25*c^3/9 + 2*c^2/3 - c) * hab
  have hn : 0 ≤ (27*a^3*c^2 + 9*a^3 + 27*a^2*b^3 - 81*a^2*b^2*c^2 - 18*a^2*b^2 + 9*a^2*b - 18*a^2*c^2 - 3*a^2 + 9*a*c^2 + 3*a + 9*b^3 + 27*b^2*c^3 - 18*b^2*c^2 + 9*b^2*c - 3*b^2 + 3*b + 9*c^3 - 3*c^2 + 3*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3), (3 * a + 1) / (3 * b ^ 2 + 1) + (3 * b + 1) / (3 * c ^ 2 + 1) + (3 * c + 1) / (3 * a ^ 2 + 1) ≥ 3) := @solution
#print axioms solution
