-- Prove2me | solution 1 for WorkbookSource.base_9999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:12:29.988413+00:00
-- url     : https://prove2.me/submissions/06c52dda-fd9c-4fb2-895d-80910bafd23b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) + 8 ≥ 9 * (a + b + c + d) ^ 2 / (a * b + b * c + c * d + a * d + a * c + b * d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 3*a^2*b^2*c^2 - 2*a^2*b^2*c*d + 3*a^2*b^2*d^2 + a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 3*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 2*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 3*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*((a)*(((b - a))*(9*((b - a)) + 12*((c - b)) + 6*((d - c))) + ((c - b))*(12*((c - b)) + 12*((d - c))) + 9*((d - c))^2) + ((b - a))*(((b - a))*(36*((b - a)) + 72*((c - b)) + 36*((d - c))) + ((c - b))*(60*((c - b)) + 60*((d - c))) + 24*((d - c))^2) + ((c - b))*(((c - b))*(24*((c - b)) + 36*((d - c))) + 12*((d - c))^2)) + ((b - a))*(((b - a))*(((b - a))*(54*((b - a)) + 144*((c - b)) + 72*((d - c))) + ((c - b))*(142*((c - b)) + 142*((d - c))) + 34*((d - c))^2) + ((c - b))*(((c - b))*(68*((c - b)) + 102*((d - c))) + 34*((d - c))^2)) + ((c - b))^2*(((c - b))*(16*((c - b)) + 32*((d - c))) + 16*((d - c))^2)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(36*((b - a)) + 120*((c - b)) + 60*((d - c))) + ((c - b))*(150*((c - b)) + 150*((d - c))) + 30*((d - c))^2) + ((c - b))*(((c - b))*(88*((c - b)) + 132*((d - c))) + 48*((d - c))^2) + 2*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(26*((c - b)) + 52*((d - c))) + 28*((d - c))^2) + 2*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(4*((c - b)) + 10*((d - c))) + 8*((d - c))^2) + 2*((d - c))^3)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((b - a))*(9*((b - a)) + 36*((c - b)) + 18*((d - c))) + ((c - b))*(56*((c - b)) + 56*((d - c))) + 11*((d - c))^2) + ((c - b))*(((c - b))*(42*((c - b)) + 63*((d - c))) + 25*((d - c))^2) + 2*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(15*((c - b)) + 30*((d - c))) + 18*((d - c))^2) + 3*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(2*((c - b)) + 5*((d - c))) + 4*((d - c))^2) + ((d - c))^3)) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 3*a^2*b^2*c^2 - 2*a^2*b^2*c*d + 3*a^2*b^2*d^2 + a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 3*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 2*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 3*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by
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
  have hn : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 3*a^2*b^2*c^2 - 2*a^2*b^2*c*d + 3*a^2*b^2*d^2 + a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 3*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 2*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 3*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (a*b*c*d*(a*b + a*c + a*d + b*c + b*d + c*d)) := by positivity
  have heqrat : ( (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) + 8 ) - ( 9 * (a + b + c + d) ^ 2 / (a * b + b * c + c * d + a * d + a * c + b * d)  ) = (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 3*a^2*b^2*c^2 - 2*a^2*b^2*c*d + 3*a^2*b^2*d^2 + a^2*b*c^3 - 2*a^2*b*c^2*d - 2*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 3*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 2*a*b^2*c^2*d - 2*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 2*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 3*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) / (a*b*c*d*(a*b + a*c + a*d + b*c + b*d + c*d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) + 8 ≥ 9 * (a + b + c + d) ^ 2 / (a * b + b * c + c * d + a * d + a * c + b * d)) := @solution
#print axioms solution
