-- Prove2me | solution 1 for WorkbookSource.base_4672
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:34:08.291198+00:00
-- url     : https://prove2.me/submissions/aa98e6f3-b6f4-4e05-b216-7e22184b8ae6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :  (a^2 + b^2 + c^2 + d^2) * (1 / (a + d) + 1 / (b + d) + 1 / (c + d)) ≥ 2 * (a + b + c)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(12*((b - a)) + 16*((c - b)) + 8*((d - c))) + ((c - b))*(16*((c - b)) + 16*((d - c))) + 12*((d - c))^2) + ((b - a))*(((b - a))*(20*((b - a)) + 42*((c - b)) + 24*((d - c))) + ((c - b))*(46*((c - b)) + 52*((d - c))) + 28*((d - c))^2) + ((c - b))*(((c - b))*(20*((c - b)) + 36*((d - c))) + 32*((d - c))^2) + 12*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(8*((b - a)) + 23*((c - b)) + 14*((d - c))) + ((c - b))*(31*((c - b)) + 38*((d - c))) + 17*((d - c))^2) + ((c - b))*(((c - b))*(22*((c - b)) + 42*((d - c))) + 35*((d - c))^2) + 12*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(6*((c - b)) + 16*((d - c))) + 19*((d - c))^2) + 12*((d - c))^3) + 3*((d - c))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (d - b) := by linarith
    have hdiff3 : 0 ≤ (c - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(12*((b - a)) + 16*((d - b)) + 8*((c - d))) + ((d - b))*(16*((d - b)) + 16*((c - d))) + 12*((c - d))^2) + ((b - a))*(((b - a))*(20*((b - a)) + 42*((d - b)) + 18*((c - d))) + ((d - b))*(46*((d - b)) + 40*((c - d))) + 22*((c - d))^2) + ((d - b))*(((d - b))*(20*((d - b)) + 24*((c - d))) + 20*((c - d))^2) + 4*((c - d))^3) + ((b - a))*(((b - a))*(((b - a))*(8*((b - a)) + 23*((d - b)) + 9*((c - d))) + ((d - b))*(31*((d - b)) + 24*((c - d))) + 10*((c - d))^2) + ((d - b))*(((d - b))*(22*((d - b)) + 24*((c - d))) + 17*((c - d))^2) + 3*((c - d))^3) + ((d - b))*(((d - b))*(((d - b))*(6*((d - b)) + 8*((c - d))) + 7*((c - d))^2) + 2*((c - d))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ b) (hord3 : b ≤ c) : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by
    have hdiff1 : 0 ≤ (d - a) := by linarith
    have hdiff2 : 0 ≤ (b - d) := by linarith
    have hdiff3 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((d - a))*(12*((d - a)) + 16*((b - d)) + 8*((c - b))) + ((b - d))*(16*((b - d)) + 16*((c - b))) + 12*((c - b))^2) + ((d - a))*(((d - a))*(20*((d - a)) + 36*((b - d)) + 18*((c - b))) + ((b - d))*(40*((b - d)) + 40*((c - b))) + 22*((c - b))^2) + ((b - d))*(((b - d))*(12*((b - d)) + 18*((c - b))) + 14*((c - b))^2) + 4*((c - b))^3) + ((d - a))*(((d - a))*(((d - a))*(8*((d - a)) + 18*((b - d)) + 9*((c - b))) + ((b - d))*(23*((b - d)) + 23*((c - b))) + 10*((c - b))^2) + ((b - d))*(((b - d))*(12*((b - d)) + 18*((c - b))) + 12*((c - b))^2) + 3*((c - b))^3) + ((b - d))*(((b - d))*(((b - d))*(2*((b - d)) + 4*((c - b))) + 3*((c - b))^2) + ((c - b))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux3 (a b c d : ℝ) (hlow : 0 ≤ d) (hord1 : d ≤ a) (hord2 : a ≤ b) (hord3 : b ≤ c) : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by
    have hdiff1 : 0 ≤ (a - d) := by linarith
    have hdiff2 : 0 ≤ (b - a) := by linarith
    have hdiff3 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (d)*((d)*(((a - d))*(12*((a - d)) + 16*((b - a)) + 8*((c - b))) + ((b - a))*(16*((b - a)) + 16*((c - b))) + 12*((c - b))^2) + ((a - d))*(((a - d))*(12*((a - d)) + 24*((b - a)) + 12*((c - b))) + ((b - a))*(28*((b - a)) + 28*((c - b))) + 16*((c - b))^2) + ((b - a))*(((b - a))*(12*((b - a)) + 18*((c - b))) + 14*((c - b))^2) + 4*((c - b))^3) + ((a - d))*(((a - d))*(((a - d))*(3*((a - d)) + 8*((b - a)) + 4*((c - b))) + ((b - a))*(11*((b - a)) + 11*((c - b))) + 5*((c - b))^2) + ((b - a))*(((b - a))*(8*((b - a)) + 12*((c - b))) + 8*((c - b))^2) + 2*((c - b))^3) + ((b - a))*(((b - a))*(((b - a))*(2*((b - a)) + 4*((c - b))) + 3*((c - b))^2) + ((c - b))^3) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux3 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux2 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux1 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux3 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux2 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux1 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux3 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux2 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux1 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux3 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux2 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux1 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux3 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux2 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux1 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux3 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux2 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux1 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + d)*(b + d)*(c + d)) := by positivity
  have heqrat : (  (a^2 + b^2 + c^2 + d^2) * (1 / (a + d) + 1 / (b + d) + 1 / (c + d)) ) - ( 2 * (a + b + c)  ) = (a^3*b + a^3*c + 2*a^3*d - a^2*b*c + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - 6*a*b*c*d - 3*a*b*d^2 + a*c^3 - 3*a*c*d^2 + b^3*c + 2*b^3*d + b^2*d^2 + b*c^3 - 3*b*c*d^2 + 2*c^3*d + c^2*d^2 + 3*d^4) / ((a + d)*(b + d)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^2 + b^2 + c^2 + d^2) * (1 / (a + d) + 1 / (b + d) + 1 / (c + d)) ≥ 2 * (a + b + c)) := @solution
#print axioms solution
