-- Prove2me | solution 1 for WorkbookSource.base_22268
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:45:16.720247+00:00
-- url     : https://prove2.me/submissions/1c4210d6-8f28-4c76-9308-7571c852d2d3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) : (x^2 + y^2)/(z + k) + (y^2 + z^2)/(x + k) + (z^2 + x^2)/(y + k) ≥ 3/2 * (x + y + z - k)  := by
  have haux0 (x y z k : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) (hord3 : z ≤ k) : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hdiff3 : 0 ≤ (k - z) := by linarith
    have hpos : 0 ≤ (x)*((x)*(((y - x))*(20*((y - x)) + 24*((z - y)) + 8*((k - z))) + ((z - y))*(24*((z - y)) + 16*((k - z))) + 12*((k - z))^2) + ((y - x))*(((y - x))*(32*((y - x)) + 62*((z - y)) + 28*((k - z))) + ((z - y))*(66*((z - y)) + 56*((k - z))) + 28*((k - z))^2) + ((z - y))*(((z - y))*(28*((z - y)) + 40*((k - z))) + 32*((k - z))^2) + 12*((k - z))^3) + ((y - x))*(((y - x))*(((y - x))*(12*((y - x)) + 32*((z - y)) + 16*((k - z))) + ((z - y))*(42*((z - y)) + 41*((k - z))) + 17*((k - z))^2) + ((z - y))*(((z - y))*(30*((z - y)) + 47*((k - z))) + 35*((k - z))^2) + 12*((k - z))^3) + ((z - y))*(((z - y))*(((z - y))*(8*((z - y)) + 18*((k - z))) + 19*((k - z))^2) + 12*((k - z))^3) + 3*((k - z))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z k : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ k) (hord3 : k ≤ z) : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (k - y) := by linarith
    have hdiff3 : 0 ≤ (z - k) := by linarith
    have hpos : 0 ≤ (x)*((x)*(((y - x))*(20*((y - x)) + 24*((k - y)) + 16*((z - k))) + ((k - y))*(24*((k - y)) + 32*((z - k))) + 20*((z - k))^2) + ((y - x))*(((y - x))*(32*((y - x)) + 62*((k - y)) + 34*((z - k))) + ((k - y))*(66*((k - y)) + 76*((z - k))) + 38*((z - k))^2) + ((k - y))*(((k - y))*(28*((k - y)) + 44*((z - k))) + 36*((z - k))^2) + 8*((z - k))^3) + ((y - x))*(((y - x))*(((y - x))*(12*((y - x)) + 32*((k - y)) + 16*((z - k))) + ((k - y))*(42*((k - y)) + 43*((z - k))) + 18*((z - k))^2) + ((k - y))*(((k - y))*(30*((k - y)) + 43*((z - k))) + 31*((z - k))^2) + 6*((z - k))^3) + ((k - y))*(((k - y))*(((k - y))*(8*((k - y)) + 14*((z - k))) + 13*((z - k))^2) + 4*((z - k))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z k : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ k) (hord2 : k ≤ y) (hord3 : y ≤ z) : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by
    have hdiff1 : 0 ≤ (k - x) := by linarith
    have hdiff2 : 0 ≤ (y - k) := by linarith
    have hdiff3 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (x)*((x)*(((k - x))*(20*((k - x)) + 32*((y - k)) + 16*((z - y))) + ((y - k))*(24*((y - k)) + 24*((z - y))) + 20*((z - y))^2) + ((k - x))*(((k - x))*(32*((k - x)) + 68*((y - k)) + 34*((z - y))) + ((y - k))*(68*((y - k)) + 68*((z - y))) + 38*((z - y))^2) + ((y - k))*(((y - k))*(20*((y - k)) + 30*((z - y))) + 26*((z - y))^2) + 8*((z - y))^3) + ((k - x))*(((k - x))*(((k - x))*(12*((k - x)) + 32*((y - k)) + 16*((z - y))) + ((y - k))*(41*((y - k)) + 41*((z - y))) + 18*((z - y))^2) + ((y - k))*(((y - k))*(22*((y - k)) + 33*((z - y))) + 23*((z - y))^2) + 6*((z - y))^3) + ((y - k))*(((y - k))*(((y - k))*(4*((y - k)) + 8*((z - y))) + 6*((z - y))^2) + 2*((z - y))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux3 (x y z k : ℝ) (hlow : 0 ≤ k) (hord1 : k ≤ x) (hord2 : x ≤ y) (hord3 : y ≤ z) : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by
    have hdiff1 : 0 ≤ (x - k) := by linarith
    have hdiff2 : 0 ≤ (y - x) := by linarith
    have hdiff3 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (k)*((k)*(((x - k))*(12*((x - k)) + 16*((y - x)) + 8*((z - y))) + ((y - x))*(24*((y - x)) + 24*((z - y))) + 20*((z - y))^2) + ((x - k))*(((x - k))*(12*((x - k)) + 24*((y - x)) + 12*((z - y))) + ((y - x))*(40*((y - x)) + 40*((z - y))) + 28*((z - y))^2) + ((y - x))*(((y - x))*(20*((y - x)) + 30*((z - y))) + 26*((z - y))^2) + 8*((z - y))^3) + ((x - k))*(((x - k))*(((x - k))*(3*((x - k)) + 8*((y - x)) + 4*((z - y))) + ((y - x))*(15*((y - x)) + 15*((z - y))) + 9*((z - y))^2) + ((y - x))*(((y - x))*(14*((y - x)) + 21*((z - y))) + 15*((z - y))^2) + 4*((z - y))^3) + ((y - x))*(((y - x))*(((y - x))*(4*((y - x)) + 8*((z - y))) + 6*((z - y))^2) + 2*((z - y))^3) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by
    rcases le_total y x with hcase1 | hcase1
    ·
      rcases le_total z y with hcase2 | hcase2
      ·
        rcases le_total k z with hcase3 | hcase3
        ·
          convert haux3 z y x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total k y with hcase4 | hcase4
          ·
            convert haux2 z y x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k x with hcase5 | hcase5
            ·
              convert haux1 z y x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 z y x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total z x with hcase6 | hcase6
        ·
          rcases le_total k y with hcase7 | hcase7
          ·
            convert haux3 y z x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k z with hcase8 | hcase8
            ·
              convert haux2 y z x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total k x with hcase9 | hcase9
              ·
                convert haux1 y z x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 y z x k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total k y with hcase10 | hcase10
          ·
            convert haux3 y x z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k x with hcase11 | hcase11
            ·
              convert haux2 y x z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total k z with hcase12 | hcase12
              ·
                convert haux1 y x z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 y x z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total z x with hcase13 | hcase13
      ·
        rcases le_total k z with hcase14 | hcase14
        ·
          convert haux3 z x y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total k x with hcase15 | hcase15
          ·
            convert haux2 z x y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k y with hcase16 | hcase16
            ·
              convert haux1 z x y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 z x y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total z y with hcase17 | hcase17
        ·
          rcases le_total k x with hcase18 | hcase18
          ·
            convert haux3 x z y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k z with hcase19 | hcase19
            ·
              convert haux2 x z y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total k y with hcase20 | hcase20
              ·
                convert haux1 x z y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 x z y k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total k x with hcase21 | hcase21
          ·
            convert haux3 x y z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total k y with hcase22 | hcase22
            ·
              convert haux2 x y z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total k z with hcase23 | hcase23
              ·
                convert haux1 x y z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 x y z k (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (2*(k + x)*(k + y)*(k + z)) := by positivity
  have heqrat : ( (x^2 + y^2)/(z + k) + (y^2 + z^2)/(x + k) + (z^2 + x^2)/(y + k) ) - ( 3/2 * (x + y + z - k)  ) = (3*k^4 + k^2*x^2 - 3*k^2*x*y - 3*k^2*x*z + k^2*y^2 - 3*k^2*y*z + k^2*z^2 + 4*k*x^3 - k*x^2*y - k*x^2*z - k*x*y^2 - 6*k*x*y*z - k*x*z^2 + 4*k*y^3 - k*y^2*z - k*y*z^2 + 4*k*z^3 + 2*x^3*y + 2*x^3*z - 3*x^2*y*z + 2*x*y^3 - 3*x*y^2*z - 3*x*y*z^2 + 2*x*z^3 + 2*y^3*z + 2*y*z^3) / (2*(k + x)*(k + y)*(k + z)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k), (x^2 + y^2)/(z + k) + (y^2 + z^2)/(x + k) + (z^2 + x^2)/(y + k) ≥ 3/2 * (x + y + z - k)) := @solution
#print axioms solution
