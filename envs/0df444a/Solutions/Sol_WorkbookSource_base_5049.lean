-- Prove2me | solution 1 for WorkbookSource.base_5049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:43:40.366215+00:00
-- url     : https://prove2.me/submissions/3bc7a472-9532-4b53-9b5d-60cb909aaa51

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b * c) / (d + a) + (b^2 + c * d) / (a + b) + (c^2 + d * a) / (b + c) + (d^2 + a * b) / (c + d) ≥ a + b + c + d  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(((b - a))*(8*((b - a)) + 16*((c - b))) + ((c - b))*(16*((c - b)) + 16*((d - c))) + 8*((d - c))^2) + ((b - a))*(((b - a))*(20*((b - a)) + 52*((c - b)) + 8*((d - c))) + ((c - b))*(60*((c - b)) + 48*((d - c))) + 16*((d - c))^2) + ((c - b))*(((c - b))*(24*((c - b)) + 36*((d - c))) + 20*((d - c))^2) + 4*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(16*((b - a)) + 51*((c - b)) + 13*((d - c))) + ((c - b))*(71*((c - b)) + 57*((d - c))) + 14*((d - c))^2) + ((c - b))*(((c - b))*(48*((c - b)) + 70*((d - c))) + 33*((d - c))^2) + 5*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(12*((c - b)) + 24*((d - c))) + 15*((d - c))^2) + 3*((d - c))^3)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(4*((b - a)) + 15*((c - b)) + 5*((d - c))) + ((c - b))*(25*((c - b)) + 22*((d - c))) + 5*((d - c))^2) + ((c - b))*(((c - b))*(23*((c - b)) + 35*((d - c))) + 16*((d - c))^2) + 2*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(11*((c - b)) + 23*((d - c))) + 15*((d - c))^2) + 3*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(2*((c - b)) + 5*((d - c))) + 4*((d - c))^2) + ((d - c))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (d - b) := by linarith
    have hdiff3 : 0 ≤ (c - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(((b - a))*(8*((b - a)) + 16*((d - b)) + 16*((c - d))) + ((d - b))*(16*((d - b)) + 16*((c - d))) + 8*((c - d))^2) + ((b - a))*(((b - a))*(20*((b - a)) + 52*((d - b)) + 44*((c - d))) + ((d - b))*(60*((d - b)) + 72*((c - d))) + 28*((c - d))^2) + ((d - b))*(((d - b))*(24*((d - b)) + 36*((c - d))) + 20*((c - d))^2) + 4*((c - d))^3) + ((b - a))*(((b - a))*(((b - a))*(16*((b - a)) + 51*((d - b)) + 38*((c - d))) + ((d - b))*(71*((d - b)) + 85*((c - d))) + 28*((c - d))^2) + ((d - b))*(((d - b))*(48*((d - b)) + 74*((c - d))) + 37*((c - d))^2) + 6*((c - d))^3) + ((d - b))*(((d - b))*(((d - b))*(12*((d - b)) + 24*((c - d))) + 15*((c - d))^2) + 3*((c - d))^3)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(4*((b - a)) + 15*((d - b)) + 10*((c - d))) + ((d - b))*(25*((d - b)) + 28*((c - d))) + 8*((c - d))^2) + ((d - b))*(((d - b))*(23*((d - b)) + 34*((c - d))) + 15*((c - d))^2) + 2*((c - d))^3) + ((d - b))*(((d - b))*(((d - b))*(11*((d - b)) + 21*((c - d))) + 12*((c - d))^2) + 2*((c - d))^3)) + ((d - b))^2*(((d - b))*(((d - b))*(2*((d - b)) + 5*((c - d))) + 4*((c - d))^2) + ((c - d))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hdiff3 : 0 ≤ (d - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(8*((c - a))^2 + 8*((d - b))^2) + ((c - a))*(((c - a))*(20*((c - a)) + 16*((b - c)) + 8*((d - b))) + 16*((d - b))^2) + 8*((b - c))*((d - b))^2 + 4*((d - b))^3) + ((c - a))*(((c - a))*(((c - a))*(16*((c - a)) + 26*((b - c)) + 13*((d - b))) + ((b - c))*(10*((b - c)) + 10*((d - b))) + 14*((d - b))^2) + 10*((b - c))*((d - b))^2 + 5*((d - b))^3) + ((b - c))*(2*((b - c))*((d - b))^2 + 2*((d - b))^3)) + ((c - a))*(((c - a))*(((c - a))*(((c - a))*(4*((c - a)) + 10*((b - c)) + 5*((d - b))) + ((b - c))*(8*((b - c)) + 8*((d - b))) + 5*((d - b))^2) + ((b - c))*(((b - c))*(2*((b - c)) + 3*((d - b))) + 5*((d - b))^2) + 2*((d - b))^3) + ((b - c))*(((b - c))*((d - b))^2 + ((d - b))^3)) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux0 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux1 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
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
            convert haux2 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux2 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux0 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux2 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux2 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux0 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux1 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux2 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux2 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux1 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux0 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux2 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux2 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux1 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux1 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (a^2 + b * c) / (d + a) + (b^2 + c * d) / (a + b) + (c^2 + d * a) / (b + c) + (d^2 + a * b) / (c + d) ) - ( a + b + c + d  ) = (a^3*b^2 + a^3*b*c + a^3*c*d + a^3*d^2 + a^2*b^3 - 2*a^2*b*c^2 - 2*a^2*b*c*d - 2*a^2*c^2*d + a^2*d^3 + a*b^3*d - 2*a*b^2*c*d - 2*a*b^2*d^2 + a*b*c^3 - 2*a*b*c^2*d - 2*a*b*c*d^2 + a*b*d^3 + a*c^3*d + b^3*c^2 + b^3*c*d + b^2*c^3 - 2*b^2*c*d^2 + b*c*d^3 + c^3*d^2 + c^2*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^2 + b * c) / (d + a) + (b^2 + c * d) / (a + b) + (c^2 + d * a) / (b + c) + (d^2 + a * b) / (c + d) ≥ a + b + c + d) := @solution
#print axioms solution
