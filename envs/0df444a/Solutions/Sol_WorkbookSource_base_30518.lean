-- Prove2me | solution 1 for WorkbookSource.base_30518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:24:13.416421+00:00
-- url     : https://prove2.me/submissions/287c3ad8-edfc-4c18-b278-084298effa5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hab : a + b + c + d = 4) : 1 / a + 1 / b + 1 / c + 1 / d ≥ 32 / (4 + a * b * c + b * c * d + c * d * a + d * a * b)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^4*b*c/16 + a^4*b*d/16 + a^4*c*d/16 + 3*a^3*b^2*c/16 + 3*a^3*b^2*d/16 + 3*a^3*b*c^2/16 - 11*a^3*b*c*d/8 + 3*a^3*b*d^2/16 + 3*a^3*c^2*d/16 + 3*a^3*c*d^2/16 + 3*a^2*b^3*c/16 + 3*a^2*b^3*d/16 + 11*a^2*b^2*c^2/8 - 7*a^2*b^2*c*d/8 + 11*a^2*b^2*d^2/8 + 3*a^2*b*c^3/16 - 7*a^2*b*c^2*d/8 - 7*a^2*b*c*d^2/8 + 3*a^2*b*d^3/16 + 3*a^2*c^3*d/16 + 11*a^2*c^2*d^2/8 + 3*a^2*c*d^3/16 + a*b^4*c/16 + a*b^4*d/16 + 3*a*b^3*c^2/16 - 11*a*b^3*c*d/8 + 3*a*b^3*d^2/16 + 3*a*b^2*c^3/16 - 7*a*b^2*c^2*d/8 - 7*a*b^2*c*d^2/8 + 3*a*b^2*d^3/16 + a*b*c^4/16 - 11*a*b*c^3*d/8 - 7*a*b*c^2*d^2/8 - 11*a*b*c*d^3/8 + a*b*d^4/16 + a*c^4*d/16 + 3*a*c^3*d^2/16 + 3*a*c^2*d^3/16 + a*c*d^4/16 + b^4*c*d/16 + 3*b^3*c^2*d/16 + 3*b^3*c*d^2/16 + 3*b^2*c^3*d/16 + 11*b^2*c^2*d^2/8 + 3*b^2*c*d^3/16 + b*c^4*d/16 + 3*b*c^3*d^2/16 + 3*b*c^2*d^3/16 + b*c*d^4/16) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*((a)*(((b - a))*(3*((b - a)) + 4*((c - b)) + 2*((d - c))) + ((c - b))*(4*((c - b)) + 4*((d - c))) + 3*((d - c))^2) + ((b - a))*(((b - a))*(23*((b - a))/2 + 23*((c - b)) + 23*((d - c))/2) + ((c - b))*(20*((c - b)) + 20*((d - c))) + 17*((d - c))^2/2) + ((c - b))*(((c - b))*(8*((c - b)) + 12*((d - c))) + 5*((d - c))^2) + ((d - c))^3/2) + ((b - a))*(((b - a))*(((b - a))*(267*((b - a))/16 + 89*((c - b))/2 + 89*((d - c))/4) + ((c - b))*(45*((c - b)) + 45*((d - c))) + 93*((d - c))^2/8) + ((c - b))*(((c - b))*(22*((c - b)) + 33*((d - c))) + 27*((d - c))^2/2) + 5*((d - c))^3/4) + ((c - b))*(((c - b))*(((c - b))*(5*((c - b)) + 10*((d - c))) + 6*((d - c))^2) + ((d - c))^3) + 3*((d - c))^4/16) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(87*((b - a))/8 + 145*((c - b))/4 + 145*((d - c))/8) + ((c - b))*(365*((c - b))/8 + 365*((d - c))/8) + 75*((d - c))^2/8) + ((c - b))*(((c - b))*(107*((c - b))/4 + 321*((d - c))/8) + 129*((d - c))^2/8) + 11*((d - c))^3/8) + ((c - b))*(((c - b))*(((c - b))*(15*((c - b))/2 + 15*((d - c))) + 75*((d - c))^2/8) + 15*((d - c))^3/8) + ((d - c))^4/4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(((c - b)) + 5*((d - c))/2) + 9*((d - c))^2/4) + 7*((d - c))^3/8) + ((d - c))^4/8)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((b - a))*(43*((b - a))/16 + 43*((c - b))/4 + 43*((d - c))/8) + ((c - b))*(267*((c - b))/16 + 267*((d - c))/16) + 13*((d - c))^2/4) + ((c - b))*(((c - b))*(99*((c - b))/8 + 297*((d - c))/16) + 119*((d - c))^2/16) + 5*((d - c))^3/8) + ((c - b))*(((c - b))*(((c - b))*(17*((c - b))/4 + 17*((d - c))/2) + 85*((d - c))^2/16) + 17*((d - c))^3/16) + ((d - c))^4/16) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(((c - b))/2 + 5*((d - c))/4) + 9*((d - c))^2/8) + 7*((d - c))^3/16) + ((d - c))^4/16)) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c/16 + a^4*b*d/16 + a^4*c*d/16 + 3*a^3*b^2*c/16 + 3*a^3*b^2*d/16 + 3*a^3*b*c^2/16 - 11*a^3*b*c*d/8 + 3*a^3*b*d^2/16 + 3*a^3*c^2*d/16 + 3*a^3*c*d^2/16 + 3*a^2*b^3*c/16 + 3*a^2*b^3*d/16 + 11*a^2*b^2*c^2/8 - 7*a^2*b^2*c*d/8 + 11*a^2*b^2*d^2/8 + 3*a^2*b*c^3/16 - 7*a^2*b*c^2*d/8 - 7*a^2*b*c*d^2/8 + 3*a^2*b*d^3/16 + 3*a^2*c^3*d/16 + 11*a^2*c^2*d^2/8 + 3*a^2*c*d^3/16 + a*b^4*c/16 + a*b^4*d/16 + 3*a*b^3*c^2/16 - 11*a*b^3*c*d/8 + 3*a*b^3*d^2/16 + 3*a*b^2*c^3/16 - 7*a*b^2*c^2*d/8 - 7*a*b^2*c*d^2/8 + 3*a*b^2*d^3/16 + a*b*c^4/16 - 11*a*b*c^3*d/8 - 7*a*b*c^2*d^2/8 - 11*a*b*c*d^3/8 + a*b*d^4/16 + a*c^4*d/16 + 3*a*c^3*d^2/16 + 3*a*c^2*d^3/16 + a*c*d^4/16 + b^4*c*d/16 + 3*b^3*c^2*d/16 + 3*b^3*c*d^2/16 + 3*b^2*c^3*d/16 + 11*b^2*c^2*d^2/8 + 3*b^2*c*d^3/16 + b*c^4*d/16 + 3*b*c^3*d^2/16 + 3*b*c^2*d^3/16 + b*c*d^4/16) := by
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
            convert haux0 c d b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux0 c b d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux0 d b c a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux0 b d c a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux0 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux0 d b a c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux0 b d a c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux0 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux0 d c a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux0 c a d b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux0 d a c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux0 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux0 a c d b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux0 a d b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux0 a b d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have he : (a^2*b^2*c^2 + 2*a^2*b^2*c*d + a^2*b^2*d^2 + 2*a^2*b*c^2*d + 2*a^2*b*c*d^2 + a^2*c^2*d^2 + 2*a*b^2*c^2*d + 2*a*b^2*c*d^2 + 2*a*b*c^2*d^2 - 32*a*b*c*d + 4*a*b*c + 4*a*b*d + 4*a*c*d + b^2*c^2*d^2 + 4*b*c*d) = (a^4*b*c/16 + a^4*b*d/16 + a^4*c*d/16 + 3*a^3*b^2*c/16 + 3*a^3*b^2*d/16 + 3*a^3*b*c^2/16 - 11*a^3*b*c*d/8 + 3*a^3*b*d^2/16 + 3*a^3*c^2*d/16 + 3*a^3*c*d^2/16 + 3*a^2*b^3*c/16 + 3*a^2*b^3*d/16 + 11*a^2*b^2*c^2/8 - 7*a^2*b^2*c*d/8 + 11*a^2*b^2*d^2/8 + 3*a^2*b*c^3/16 - 7*a^2*b*c^2*d/8 - 7*a^2*b*c*d^2/8 + 3*a^2*b*d^3/16 + 3*a^2*c^3*d/16 + 11*a^2*c^2*d^2/8 + 3*a^2*c*d^3/16 + a*b^4*c/16 + a*b^4*d/16 + 3*a*b^3*c^2/16 - 11*a*b^3*c*d/8 + 3*a*b^3*d^2/16 + 3*a*b^2*c^3/16 - 7*a*b^2*c^2*d/8 - 7*a*b^2*c*d^2/8 + 3*a*b^2*d^3/16 + a*b*c^4/16 - 11*a*b*c^3*d/8 - 7*a*b*c^2*d^2/8 - 11*a*b*c*d^3/8 + a*b*d^4/16 + a*c^4*d/16 + 3*a*c^3*d^2/16 + 3*a*c^2*d^3/16 + a*c*d^4/16 + b^4*c*d/16 + 3*b^3*c^2*d/16 + 3*b^3*c*d^2/16 + 3*b^2*c^3*d/16 + 11*b^2*c^2*d^2/8 + 3*b^2*c*d^3/16 + b*c^4*d/16 + 3*b*c^3*d^2/16 + 3*b*c^2*d^3/16 + b*c*d^4/16) := by
    linear_combination (-a^3*b*c/16 - a^3*b*d/16 - a^3*c*d/16 - a^2*b^2*c/8 - a^2*b^2*d/8 - a^2*b*c^2/8 + 25*a^2*b*c*d/16 - a^2*b*c/4 - a^2*b*d^2/8 - a^2*b*d/4 - a^2*c^2*d/8 - a^2*c*d^2/8 - a^2*c*d/4 - a*b^3*c/16 - a*b^3*d/16 - a*b^2*c^2/8 + 25*a*b^2*c*d/16 - a*b^2*c/4 - a*b^2*d^2/8 - a*b^2*d/4 - a*b*c^3/16 + 25*a*b*c^2*d/16 - a*b*c^2/4 + 25*a*b*c*d^2/16 + 7*a*b*c*d - a*b*c - a*b*d^3/16 - a*b*d^2/4 - a*b*d - a*c^3*d/16 - a*c^2*d^2/8 - a*c^2*d/4 - a*c*d^3/16 - a*c*d^2/4 - a*c*d - b^3*c*d/16 - b^2*c^2*d/8 - b^2*c*d^2/8 - b^2*c*d/4 - b*c^3*d/16 - b*c^2*d^2/8 - b*c^2*d/4 - b*c*d^3/16 - b*c*d^2/4 - b*c*d) * hab
  have hn : 0 ≤ (a^2*b^2*c^2 + 2*a^2*b^2*c*d + a^2*b^2*d^2 + 2*a^2*b*c^2*d + 2*a^2*b*c*d^2 + a^2*c^2*d^2 + 2*a*b^2*c^2*d + 2*a*b^2*c*d^2 + 2*a*b*c^2*d^2 - 32*a*b*c*d + 4*a*b*c + 4*a*b*d + 4*a*c*d + b^2*c^2*d^2 + 4*b*c*d) := by nlinarith only [hp, he]
  have hd : (0 : ℝ) < (a*b*c*d*(a*b*c + a*b*d + a*c*d + b*c*d + 4)) := by positivity
  have heqrat : ( 1 / a + 1 / b + 1 / c + 1 / d ) - ( 32 / (4 + a * b * c + b * c * d + c * d * a + d * a * b)  ) = (a^2*b^2*c^2 + 2*a^2*b^2*c*d + a^2*b^2*d^2 + 2*a^2*b*c^2*d + 2*a^2*b*c*d^2 + a^2*c^2*d^2 + 2*a*b^2*c^2*d + 2*a*b^2*c*d^2 + 2*a*b*c^2*d^2 - 32*a*b*c*d + 4*a*b*c + 4*a*b*d + 4*a*c*d + b^2*c^2*d^2 + 4*b*c*d) / (a*b*c*d*(a*b*c + a*b*d + a*c*d + b*c*d + 4)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hab : a + b + c + d = 4), 1 / a + 1 / b + 1 / c + 1 / d ≥ 32 / (4 + a * b * c + b * c * d + c * d * a + d * a * b)) := @solution
#print axioms solution
