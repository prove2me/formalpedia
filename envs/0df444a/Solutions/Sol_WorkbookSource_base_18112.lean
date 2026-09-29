-- Prove2me | solution 1 for WorkbookSource.base_18112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:51:47.004718+00:00
-- url     : https://prove2.me/submissions/ccb67058-0a28-4a2f-9b4d-6f31e181a607

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (4 * (b^2 + c^2 + d^2 + a^2)) / (c + a + b + d) ≥ (b^2 + c^2 + d^2) / (c + d + b) + (c^2 + d^2 + a^2) / (c + d + a) + (d^2 + a^2 + b^2) / (b + d + a) + (a^2 + b^2 + c^2) / (a + b + c)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^5*b + a^5*c + a^5*d + 2*a^4*b*c + 2*a^4*b*d + 2*a^4*c*d - 2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 + 3*a^3*b*c*d - a^3*b*d^2 - 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 - 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d - 2*a^2*b^2*c*d - a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 + a*b^5 + 2*a*b^4*c + 2*a*b^4*d - a*b^3*c^2 + 3*a*b^3*c*d - a*b^3*d^2 - a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^4 + 3*a*b*c^3*d - 2*a*b*c^2*d^2 + 3*a*b*c*d^3 + 2*a*b*d^4 + a*c^5 + 2*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 2*a*c*d^4 + a*d^5 + b^5*c + b^5*d + 2*b^4*c*d - 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 - 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 + b*c^5 + 2*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 2*b*c*d^4 + b*d^5 + c^5*d - 2*c^3*d^3 + c*d^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*((a)*(((b - a))*(27*((b - a)) + 36*((c - b)) + 18*((d - c))) + ((c - b))*(36*((c - b)) + 36*((d - c))) + 27*((d - c))^2) + ((b - a))*(((b - a))*(63*((b - a)) + 126*((c - b)) + 63*((d - c))) + ((c - b))*(180*((c - b)) + 180*((d - c))) + 117*((d - c))^2) + ((c - b))*(((c - b))*(72*((c - b)) + 108*((d - c))) + 126*((d - c))^2) + 45*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(48*((b - a)) + 128*((c - b)) + 64*((d - c))) + ((c - b))*(253*((c - b)) + 253*((d - c))) + 157*((d - c))^2) + ((c - b))*(((c - b))*(196*((c - b)) + 294*((d - c))) + 334*((d - c))^2) + 118*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(44*((c - b)) + 88*((d - c))) + 145*((d - c))^2) + 101*((d - c))^3) + 21*((d - c))^4) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(12*((b - a)) + 40*((c - b)) + 20*((d - c))) + ((c - b))*(119*((c - b)) + 119*((d - c))) + 79*((d - c))^2) + ((c - b))*(((c - b))*(144*((c - b)) + 216*((d - c))) + 258*((d - c))^2) + 93*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(64*((c - b)) + 128*((d - c))) + 223*((d - c))^2) + 159*((d - c))^3) + 33*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(8*((c - b)) + 20*((d - c))) + 52*((d - c))^2) + 58*((d - c))^3) + 24*((d - c))^4) + 3*((d - c))^5) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((c - b))*(12*((c - b)) + 12*((d - c))) + 12*((d - c))^2) + ((c - b))*(((c - b))*(26*((c - b)) + 39*((d - c))) + 57*((d - c))^2) + 22*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(18*((c - b)) + 36*((d - c))) + 75*((d - c))^2) + 57*((d - c))^3) + 12*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(4*((c - b)) + 10*((d - c))) + 34*((d - c))^2) + 41*((d - c))^3) + 17*((d - c))^4) + 2*((d - c))^5) + ((c - b))*(((c - b))*(((c - b))*(4*((c - b))*((d - c))^2 + 8*((d - c))^3) + 5*((d - c))^4) + ((d - c))^5) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c + a^5*d + 2*a^4*b*c + 2*a^4*b*d + 2*a^4*c*d - 2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 + 3*a^3*b*c*d - a^3*b*d^2 - 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 - 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d - 2*a^2*b^2*c*d - a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 + a*b^5 + 2*a*b^4*c + 2*a*b^4*d - a*b^3*c^2 + 3*a*b^3*c*d - a*b^3*d^2 - a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^4 + 3*a*b*c^3*d - 2*a*b*c^2*d^2 + 3*a*b*c*d^3 + 2*a*b*d^4 + a*c^5 + 2*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 2*a*c*d^4 + a*d^5 + b^5*c + b^5*d + 2*b^4*c*d - 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 - 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 + b*c^5 + 2*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 2*b*c*d^4 + b*d^5 + c^5*d - 2*c^3*d^3 + c*d^5) := by
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
  have hn : 0 ≤ (a^5*b + a^5*c + a^5*d + 2*a^4*b*c + 2*a^4*b*d + 2*a^4*c*d - 2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 + 3*a^3*b*c*d - a^3*b*d^2 - 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 - 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d - 2*a^2*b^2*c*d - a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 + a*b^5 + 2*a*b^4*c + 2*a*b^4*d - a*b^3*c^2 + 3*a*b^3*c*d - a*b^3*d^2 - a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^4 + 3*a*b*c^3*d - 2*a*b*c^2*d^2 + 3*a*b*c*d^3 + 2*a*b*d^4 + a*c^5 + 2*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 2*a*c*d^4 + a*d^5 + b^5*c + b^5*d + 2*b^4*c*d - 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 - 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 + b*c^5 + 2*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 2*b*c*d^4 + b*d^5 + c^5*d - 2*c^3*d^3 + c*d^5) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)*(a + b + c + d)) := by positivity
  have heqrat : ( (4 * (b^2 + c^2 + d^2 + a^2)) / (c + a + b + d) ) - ( (b^2 + c^2 + d^2) / (c + d + b) + (c^2 + d^2 + a^2) / (c + d + a) + (d^2 + a^2 + b^2) / (b + d + a) + (a^2 + b^2 + c^2) / (a + b + c)  ) = (a^5*b + a^5*c + a^5*d + 2*a^4*b*c + 2*a^4*b*d + 2*a^4*c*d - 2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 + 3*a^3*b*c*d - a^3*b*d^2 - 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 - 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d - 2*a^2*b^2*c*d - a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 + a*b^5 + 2*a*b^4*c + 2*a*b^4*d - a*b^3*c^2 + 3*a*b^3*c*d - a*b^3*d^2 - a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^4 + 3*a*b*c^3*d - 2*a*b*c^2*d^2 + 3*a*b*c*d^3 + 2*a*b*d^4 + a*c^5 + 2*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 2*a*c*d^4 + a*d^5 + b^5*c + b^5*d + 2*b^4*c*d - 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 - 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 + b*c^5 + 2*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 2*b*c*d^4 + b*d^5 + c^5*d - 2*c^3*d^3 + c*d^5) / ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)*(a + b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (4 * (b^2 + c^2 + d^2 + a^2)) / (c + a + b + d) ≥ (b^2 + c^2 + d^2) / (c + d + b) + (c^2 + d^2 + a^2) / (c + d + a) + (d^2 + a^2 + b^2) / (b + d + a) + (a^2 + b^2 + c^2) / (a + b + c)) := @solution
#print axioms solution
