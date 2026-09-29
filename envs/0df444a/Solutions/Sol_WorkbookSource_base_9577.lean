-- Prove2me | solution 1 for WorkbookSource.base_9577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:12:29.066774+00:00
-- url     : https://prove2.me/submissions/a0a4db3b-6bfa-4624-9b2d-f51f62aba6c2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (a + b + c) + 1 / (b + c + d) + 1 / (a + c + d) + 1 / (d + a + b)) ≥ 22 / 3 * (a + b + c + d) / (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2 + 3 * a * b + 3 * b * c + 3 * c * d + 3 * a * d + 3 * a * c + 3 * b * d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (3*a^5 + 2*a^4*b + 2*a^4*c + 2*a^4*d - 3*a^3*b^2 - 3*a^3*c^2 - 3*a^3*d^2 - 3*a^2*b^3 - a^2*b^2*c - a^2*b^2*d - a^2*b*c^2 + 3*a^2*b*c*d - a^2*b*d^2 - 3*a^2*c^3 - a^2*c^2*d - a^2*c*d^2 - 3*a^2*d^3 + 2*a*b^4 - a*b^2*c^2 + 3*a*b^2*c*d - a*b^2*d^2 + 3*a*b*c^2*d + 3*a*b*c*d^2 + 2*a*c^4 - a*c^2*d^2 + 2*a*d^4 + 3*b^5 + 2*b^4*c + 2*b^4*d - 3*b^3*c^2 - 3*b^3*d^2 - 3*b^2*c^3 - b^2*c^2*d - b^2*c*d^2 - 3*b^2*d^3 + 2*b*c^4 - b*c^2*d^2 + 2*b*d^4 + 3*c^5 + 2*c^4*d - 3*c^3*d^2 - 3*c^2*d^3 + 2*c*d^4 + 3*d^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(((b - a))*(27*((b - a)) + 36*((c - b)) + 18*((d - c))) + ((c - b))*(36*((c - b)) + 36*((d - c))) + 27*((d - c))^2) + ((b - a))*(((b - a))*(36*((b - a)) + 72*((c - b)) + 36*((d - c))) + ((c - b))*(135*((c - b)) + 135*((d - c))) + 99*((d - c))^2) + ((c - b))*(((c - b))*(54*((c - b)) + 81*((d - c))) + 117*((d - c))^2) + 45*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(12*((b - a)) + 32*((c - b)) + 16*((d - c))) + ((c - b))*(121*((c - b)) + 121*((d - c))) + 97*((d - c))^2) + ((c - b))*(((c - b))*(106*((c - b)) + 159*((d - c))) + 229*((d - c))^2) + 88*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(26*((c - b)) + 52*((d - c))) + 112*((d - c))^2) + 86*((d - c))^3) + 21*((d - c))^4) + ((b - a))*(((b - a))*(((b - a))*(((c - b))*(28*((c - b)) + 28*((d - c))) + 28*((d - c))^2) + ((c - b))*(((c - b))*(44*((c - b)) + 66*((d - c))) + 102*((d - c))^2) + 40*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(23*((c - b)) + 46*((d - c))) + 101*((d - c))^2) + 78*((d - c))^3) + 19*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(4*((c - b)) + 10*((d - c))) + 30*((d - c))^2) + 35*((d - c))^3) + 17*((d - c))^4) + 3*((d - c))^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5 + 2*a^4*b + 2*a^4*c + 2*a^4*d - 3*a^3*b^2 - 3*a^3*c^2 - 3*a^3*d^2 - 3*a^2*b^3 - a^2*b^2*c - a^2*b^2*d - a^2*b*c^2 + 3*a^2*b*c*d - a^2*b*d^2 - 3*a^2*c^3 - a^2*c^2*d - a^2*c*d^2 - 3*a^2*d^3 + 2*a*b^4 - a*b^2*c^2 + 3*a*b^2*c*d - a*b^2*d^2 + 3*a*b*c^2*d + 3*a*b*c*d^2 + 2*a*c^4 - a*c^2*d^2 + 2*a*d^4 + 3*b^5 + 2*b^4*c + 2*b^4*d - 3*b^3*c^2 - 3*b^3*d^2 - 3*b^2*c^3 - b^2*c^2*d - b^2*c*d^2 - 3*b^2*d^3 + 2*b*c^4 - b*c^2*d^2 + 2*b*d^4 + 3*c^5 + 2*c^4*d - 3*c^3*d^2 - 3*c^2*d^3 + 2*c*d^4 + 3*d^5) := by
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
  have hn : 0 ≤ (3*a^5 + 2*a^4*b + 2*a^4*c + 2*a^4*d - 3*a^3*b^2 - 3*a^3*c^2 - 3*a^3*d^2 - 3*a^2*b^3 - a^2*b^2*c - a^2*b^2*d - a^2*b*c^2 + 3*a^2*b*c*d - a^2*b*d^2 - 3*a^2*c^3 - a^2*c^2*d - a^2*c*d^2 - 3*a^2*d^3 + 2*a*b^4 - a*b^2*c^2 + 3*a*b^2*c*d - a*b^2*d^2 + 3*a*b*c^2*d + 3*a*b*c*d^2 + 2*a*c^4 - a*c^2*d^2 + 2*a*d^4 + 3*b^5 + 2*b^4*c + 2*b^4*d - 3*b^3*c^2 - 3*b^3*d^2 - 3*b^2*c^3 - b^2*c^2*d - b^2*c*d^2 - 3*b^2*d^3 + 2*b*c^4 - b*c^2*d^2 + 2*b*d^4 + 3*c^5 + 2*c^4*d - 3*c^3*d^2 - 3*c^2*d^3 + 2*c*d^4 + 3*d^5) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (3*(a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)*(a^2 + 3*a*b + 3*a*c + 3*a*d + b^2 + 3*b*c + 3*b*d + c^2 + 3*c*d + d^2)) := by positivity
  have heqrat : ( (1 / (a + b + c) + 1 / (b + c + d) + 1 / (a + c + d) + 1 / (d + a + b)) ) - ( 22 / 3 * (a + b + c + d) / (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2 + 3 * a * b + 3 * b * c + 3 * c * d + 3 * a * d + 3 * a * c + 3 * b * d)  ) = (3*a^5 + 2*a^4*b + 2*a^4*c + 2*a^4*d - 3*a^3*b^2 - 3*a^3*c^2 - 3*a^3*d^2 - 3*a^2*b^3 - a^2*b^2*c - a^2*b^2*d - a^2*b*c^2 + 3*a^2*b*c*d - a^2*b*d^2 - 3*a^2*c^3 - a^2*c^2*d - a^2*c*d^2 - 3*a^2*d^3 + 2*a*b^4 - a*b^2*c^2 + 3*a*b^2*c*d - a*b^2*d^2 + 3*a*b*c^2*d + 3*a*b*c*d^2 + 2*a*c^4 - a*c^2*d^2 + 2*a*d^4 + 3*b^5 + 2*b^4*c + 2*b^4*d - 3*b^3*c^2 - 3*b^3*d^2 - 3*b^2*c^3 - b^2*c^2*d - b^2*c*d^2 - 3*b^2*d^3 + 2*b*c^4 - b*c^2*d^2 + 2*b*d^4 + 3*c^5 + 2*c^4*d - 3*c^3*d^2 - 3*c^2*d^3 + 2*c*d^4 + 3*d^5) / (3*(a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)*(a^2 + 3*a*b + 3*a*c + 3*a*d + b^2 + 3*b*c + 3*b*d + c^2 + 3*c*d + d^2)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (1 / (a + b + c) + 1 / (b + c + d) + 1 / (a + c + d) + 1 / (d + a + b)) ≥ 22 / 3 * (a + b + c + d) / (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2 + 3 * a * b + 3 * b * c + 3 * c * d + 3 * a * d + 3 * a * c + 3 * b * d)) := @solution
#print axioms solution
