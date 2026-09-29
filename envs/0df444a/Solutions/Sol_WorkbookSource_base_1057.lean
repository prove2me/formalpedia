-- Prove2me | solution 1 for WorkbookSource.base_1057
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:28:35.149586+00:00
-- url     : https://prove2.me/submissions/f7ac7701-a253-4338-a927-8bcdd65ecb2d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a + b) + 1 / (b + c) + 1 / (c + d) + 1 / (d + a) + 1 / (c + a) + 1 / (b + d) ≥ 9 / 2 * (a + b + c + d) / (a * b + b * c + c * d + d * a + a * c + b * d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (2*a^4*b^3 - a^4*b^2*c - a^4*b^2*d - a^4*b*c^2 - a^4*b*d^2 + 2*a^4*c^3 - a^4*c^2*d - a^4*c*d^2 + 2*a^4*d^3 + 2*a^3*b^4 - 2*a^3*b^2*c^2 - 2*a^3*b^2*d^2 + 2*a^3*c^4 - 2*a^3*c^2*d^2 + 2*a^3*d^4 - a^2*b^4*c - a^2*b^4*d - 2*a^2*b^3*c^2 - 2*a^2*b^3*d^2 - 2*a^2*b^2*c^3 + 6*a^2*b^2*c^2*d + 6*a^2*b^2*c*d^2 - 2*a^2*b^2*d^3 - a^2*b*c^4 + 6*a^2*b*c^2*d^2 - a^2*b*d^4 - a^2*c^4*d - 2*a^2*c^3*d^2 - 2*a^2*c^2*d^3 - a^2*c*d^4 - a*b^4*c^2 - a*b^4*d^2 - a*b^2*c^4 + 6*a*b^2*c^2*d^2 - a*b^2*d^4 - a*c^4*d^2 - a*c^2*d^4 + 2*b^4*c^3 - b^4*c^2*d - b^4*c*d^2 + 2*b^4*d^3 + 2*b^3*c^4 - 2*b^3*c^2*d^2 + 2*b^3*d^4 - b^2*c^4*d - 2*b^2*c^3*d^2 - 2*b^2*c^2*d^3 - b^2*c*d^4 - b*c^4*d^2 - b*c^2*d^4 + 2*c^4*d^3 + 2*c^3*d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(((b - a))*(((b - a))*(((c - b))*(32*((c - b)) + 32*((d - c))) + 32*((d - c))^2) + ((c - b))*(((c - b))*(64*((c - b)) + 96*((d - c))) + 32*((d - c))^2)) + ((c - b))^2*(((c - b))*(32*((c - b)) + 64*((d - c))) + 32*((d - c))^2)) + ((b - a))*(((b - a))*(((b - a))*(((c - b))*(72*((c - b)) + 72*((d - c))) + 72*((d - c))^2) + ((c - b))*(((c - b))*(192*((c - b)) + 288*((d - c))) + 144*((d - c))^2) + 24*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(168*((c - b)) + 336*((d - c))) + 192*((d - c))^2) + 24*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(48*((c - b)) + 120*((d - c))) + 96*((d - c))^2) + 24*((d - c))^3)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((c - b))*(52*((c - b)) + 52*((d - c))) + 52*((d - c))^2) + ((c - b))*(((c - b))*(176*((c - b)) + 264*((d - c))) + 152*((d - c))^2) + 32*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(220*((c - b)) + 440*((d - c))) + 276*((d - c))^2) + 56*((d - c))^3) + 4*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(120*((c - b)) + 300*((d - c))) + 248*((d - c))^2) + 72*((d - c))^3) + 4*((d - c))^4)) + ((c - b))^2*(((c - b))*(((c - b))*(((c - b))*(24*((c - b)) + 72*((d - c))) + 76*((d - c))^2) + 32*((d - c))^3) + 4*((d - c))^4)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((b - a))*(((c - b))*(12*((c - b)) + 12*((d - c))) + 12*((d - c))^2) + ((c - b))*(((c - b))*(50*((c - b)) + 75*((d - c))) + 45*((d - c))^2) + 10*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(82*((c - b)) + 164*((d - c))) + 106*((d - c))^2) + 24*((d - c))^3) + 2*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(66*((c - b)) + 165*((d - c))) + 138*((d - c))^2) + 42*((d - c))^3) + 3*((d - c))^4)) + ((c - b))^2*(((c - b))*(((c - b))*(((c - b))*(26*((c - b)) + 78*((d - c))) + 83*((d - c))^2) + 36*((d - c))^3) + 5*((d - c))^4)) + ((c - b))^3*(((c - b))*(((c - b))*(((c - b))*(4*((c - b)) + 14*((d - c))) + 18*((d - c))^2) + 10*((d - c))^3) + 2*((d - c))^4) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^3 - a^4*b^2*c - a^4*b^2*d - a^4*b*c^2 - a^4*b*d^2 + 2*a^4*c^3 - a^4*c^2*d - a^4*c*d^2 + 2*a^4*d^3 + 2*a^3*b^4 - 2*a^3*b^2*c^2 - 2*a^3*b^2*d^2 + 2*a^3*c^4 - 2*a^3*c^2*d^2 + 2*a^3*d^4 - a^2*b^4*c - a^2*b^4*d - 2*a^2*b^3*c^2 - 2*a^2*b^3*d^2 - 2*a^2*b^2*c^3 + 6*a^2*b^2*c^2*d + 6*a^2*b^2*c*d^2 - 2*a^2*b^2*d^3 - a^2*b*c^4 + 6*a^2*b*c^2*d^2 - a^2*b*d^4 - a^2*c^4*d - 2*a^2*c^3*d^2 - 2*a^2*c^2*d^3 - a^2*c*d^4 - a*b^4*c^2 - a*b^4*d^2 - a*b^2*c^4 + 6*a*b^2*c^2*d^2 - a*b^2*d^4 - a*c^4*d^2 - a*c^2*d^4 + 2*b^4*c^3 - b^4*c^2*d - b^4*c*d^2 + 2*b^4*d^3 + 2*b^3*c^4 - 2*b^3*c^2*d^2 + 2*b^3*d^4 - b^2*c^4*d - 2*b^2*c^3*d^2 - 2*b^2*c^2*d^3 - b^2*c*d^4 - b*c^4*d^2 - b*c^2*d^4 + 2*c^4*d^3 + 2*c^3*d^4) := by
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
  have hn : 0 ≤ ((a + b + c + d)*(2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 + 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 + 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d + 2*a^2*b^2*c*d - a^2*b*c^3 + 2*a^2*b*c^2*d + 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 + 2*a*b^2*c^2*d + 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^2*d^2 - a*c^3*d^2 - a*c^2*d^3 + 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 + 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 - b*c^3*d^2 - b*c^2*d^3 + 2*c^3*d^3)) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (2*(a + b)*(a + c)*(a + d)*(b + c)*(b + d)*(c + d)*(a*b + a*c + a*d + b*c + b*d + c*d)) := by positivity
  have heqrat : ( 1 / (a + b) + 1 / (b + c) + 1 / (c + d) + 1 / (d + a) + 1 / (c + a) + 1 / (b + d) ) - ( 9 / 2 * (a + b + c + d) / (a * b + b * c + c * d + d * a + a * c + b * d)  ) = ((a + b + c + d)*(2*a^3*b^3 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 + 2*a^3*c^3 - a^3*c^2*d - a^3*c*d^2 + 2*a^3*d^3 - a^2*b^3*c - a^2*b^3*d + 2*a^2*b^2*c*d - a^2*b*c^3 + 2*a^2*b*c^2*d + 2*a^2*b*c*d^2 - a^2*b*d^3 - a^2*c^3*d - a^2*c*d^3 - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 + 2*a*b^2*c^2*d + 2*a*b^2*c*d^2 - a*b^2*d^3 + 2*a*b*c^2*d^2 - a*c^3*d^2 - a*c^2*d^3 + 2*b^3*c^3 - b^3*c^2*d - b^3*c*d^2 + 2*b^3*d^3 - b^2*c^3*d - b^2*c*d^3 - b*c^3*d^2 - b*c^2*d^3 + 2*c^3*d^3)) / (2*(a + b)*(a + c)*(a + d)*(b + c)*(b + d)*(c + d)*(a*b + a*c + a*d + b*c + b*d + c*d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), 1 / (a + b) + 1 / (b + c) + 1 / (c + d) + 1 / (d + a) + 1 / (c + a) + 1 / (b + d) ≥ 9 / 2 * (a + b + c + d) / (a * b + b * c + c * d + d * a + a * c + b * d)) := @solution
#print axioms solution
