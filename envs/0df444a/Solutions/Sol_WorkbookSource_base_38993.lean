-- Prove2me | solution 1 for WorkbookSource.base_38993
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:36.057919+00:00
-- url     : https://prove2.me/submissions/e161e92d-5fb2-4d1e-886d-07dd85a56eef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 6) : 100 + 5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) - a ^ 2 * b ^ 2 * c ^ 2 ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (35*a^6/5832 + 55*a^5*b/1944 + 55*a^5*c/1944 + 7*a^4*b^2/1944 + 215*a^4*b*c/1944 + 7*a^4*c^2/1944 - 109*a^3*b^3/2916 + 77*a^3*b^2*c/972 + 77*a^3*b*c^2/972 - 109*a^3*c^3/2916 + 7*a^2*b^4/1944 + 77*a^2*b^3*c/972 - 293*a^2*b^2*c^2/324 + 77*a^2*b*c^3/972 + 7*a^2*c^4/1944 + 55*a*b^5/1944 + 215*a*b^4*c/1944 + 77*a*b^3*c^2/972 + 77*a*b^2*c^3/972 + 215*a*b*c^4/1944 + 55*a*c^5/1944 + 35*b^6/5832 + 55*b^5*c/1944 + 7*b^4*c^2/1944 - 109*b^3*c^3/2916 + 7*b^2*c^4/1944 + 55*b*c^5/1944 + 35*c^6/5832) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7/8 : ℝ) * a^4 * (b - a)^2 + (7/8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (7/8 : ℝ) * a^4 * (c - b)^2 + (61/27 : ℝ) * a^3 * (b - a)^3 + (61/18 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (65/18 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (67/54 : ℝ) * a^3 * (c - b)^3 + (109/54 : ℝ) * a^2 * (b - a)^4 + (109/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (175/36 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (307/108 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (53/108 : ℝ) * a^2 * (c - b)^4 + (2/3 : ℝ) * a^1 * (b - a)^5 + (5/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (65/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (35/18 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (13/18 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (5/54 : ℝ) * a^1 * (c - b)^5 + (28/729 : ℝ) * (b - a)^6 + (28/243 : ℝ) * (b - a)^5 * (c - b)^1 + (139/486 : ℝ) * (b - a)^4 * (c - b)^2 + (277/729 : ℝ) * (b - a)^3 * (c - b)^3 + (457/1944 : ℝ) * (b - a)^2 * (c - b)^4 + (125/1944 : ℝ) * (b - a)^1 * (c - b)^5 + (35/5832 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (35*a^6/5832 + 55*a^5*b/1944 + 55*a^5*c/1944 + 7*a^4*b^2/1944 + 215*a^4*b*c/1944 + 7*a^4*c^2/1944 - 109*a^3*b^3/2916 + 77*a^3*b^2*c/972 + 77*a^3*b*c^2/972 - 109*a^3*c^3/2916 + 7*a^2*b^4/1944 + 77*a^2*b^3*c/972 - 293*a^2*b^2*c^2/324 + 77*a^2*b*c^3/972 + 7*a^2*c^4/1944 + 55*a*b^5/1944 + 215*a*b^4*c/1944 + 77*a*b^3*c^2/972 + 77*a*b^2*c^3/972 + 215*a*b*c^4/1944 + 55*a*c^5/1944 + 35*b^6/5832 + 55*b^5*c/1944 + 7*b^4*c^2/1944 - 109*b^3*c^3/2916 + 7*b^2*c^4/1944 + 55*b*c^5/1944 + 35*c^6/5832) := by
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
  have he : (-a^2*b^2*c^2 - 2*a^2*b^2 - 2*a^2*c^2 + 5*a^2 - 2*b^2*c^2 + 5*b^2 + 5*c^2 + 100) = (35*a^6/5832 + 55*a^5*b/1944 + 55*a^5*c/1944 + 7*a^4*b^2/1944 + 215*a^4*b*c/1944 + 7*a^4*c^2/1944 - 109*a^3*b^3/2916 + 77*a^3*b^2*c/972 + 77*a^3*b*c^2/972 - 109*a^3*c^3/2916 + 7*a^2*b^4/1944 + 77*a^2*b^3*c/972 - 293*a^2*b^2*c^2/324 + 77*a^2*b*c^3/972 + 7*a^2*c^4/1944 + 55*a*b^5/1944 + 215*a*b^4*c/1944 + 77*a*b^3*c^2/972 + 77*a*b^2*c^3/972 + 215*a*b*c^4/1944 + 55*a*c^5/1944 + 35*b^6/5832 + 55*b^5*c/1944 + 7*b^4*c^2/1944 - 109*b^3*c^3/2916 + 7*b^2*c^4/1944 + 55*b*c^5/1944 + 35*c^6/5832) := by
    linear_combination (-35*a^5/5832 - 65*a^4*b/2916 - 65*a^4*c/2916 - 35*a^4/972 + 109*a^3*b^2/5832 - 385*a^3*b*c/5832 - 95*a^3*b/972 + 109*a^3*c^2/5832 - 95*a^3*c/972 - 35*a^3/162 + 109*a^2*b^3/5832 - 31*a^2*b^2*c/972 + 17*a^2*b^2/81 - 31*a^2*b*c^2/972 - 65*a^2*b*c/324 - 10*a^2*b/27 + 109*a^2*c^3/5832 + 17*a^2*c^2/81 - 10*a^2*c/27 - 35*a^2/27 - 65*a*b^4/2916 - 385*a*b^3*c/5832 - 95*a*b^3/972 - 31*a*b^2*c^2/972 - 65*a*b^2*c/324 - 10*a*b^2/27 - 385*a*b*c^3/5832 - 65*a*b*c^2/324 - 25*a*b*c/54 - 25*a*b/27 - 65*a*c^4/2916 - 95*a*c^3/972 - 10*a*c^2/27 - 25*a*c/27 - 25*a/9 - 35*b^5/5832 - 65*b^4*c/2916 - 35*b^4/972 + 109*b^3*c^2/5832 - 95*b^3*c/972 - 35*b^3/162 + 109*b^2*c^3/5832 + 17*b^2*c^2/81 - 10*b^2*c/27 - 35*b^2/27 - 65*b*c^4/2916 - 95*b*c^3/972 - 10*b*c^2/27 - 25*b*c/27 - 25*b/9 - 35*c^5/5832 - 35*c^4/972 - 35*c^3/162 - 35*c^2/27 - 25*c/9 - 50/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 6), 100 + 5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) - a ^ 2 * b ^ 2 * c ^ 2 ≥ 0) := @solution
#print axioms solution
