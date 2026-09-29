-- Prove2me | solution 1 for WorkbookSource.plus_61764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:00:46.295848+00:00
-- url     : https://prove2.me/submissions/8b275f44-e3a6-4981-ace6-66504b980510

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + a * b * c + b * c * d + c * d * a + d * a * b ≥ 1 / 2 * (a * b * c * d + 15)   := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (17*a^4/256 + a^3*b/64 + a^3*c/64 + a^3*d/64 - 13*a^2*b^2/128 + 3*a^2*b*c/64 + 3*a^2*b*d/64 - 13*a^2*c^2/128 + 3*a^2*c*d/64 - 13*a^2*d^2/128 + a*b^3/64 + 3*a*b^2*c/64 + 3*a*b^2*d/64 + 3*a*b*c^2/64 - 13*a*b*c*d/32 + 3*a*b*d^2/64 + a*c^3/64 + 3*a*c^2*d/64 + 3*a*c*d^2/64 + a*d^3/64 + 17*b^4/256 + b^3*c/64 + b^3*d/64 - 13*b^2*c^2/128 + 3*b^2*c*d/64 - 13*b^2*d^2/128 + b*c^3/64 + 3*b*c^2*d/64 + 3*b*c*d^2/64 + b*d^3/64 + 17*c^4/256 + c^3*d/64 - 13*c^2*d^2/128 + c*d^3/64 + 17*d^4/256) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(3*((b - a))/8 + ((c - b))/2 + ((d - c))/4) + ((c - b))*(((c - b))/2 + ((d - c))/2) + 3*((d - c))^2/8) + ((b - a))*(((b - a))*(7*((b - a))/16 + 7*((c - b))/8 + 7*((d - c))/16) + ((c - b))*(5*((c - b))/4 + 5*((d - c))/4) + 13*((d - c))^2/16) + ((c - b))*(((c - b))*(((c - b))/2 + 3*((d - c))/4) + 7*((d - c))^2/8) + 5*((d - c))^3/16) + ((b - a))*(((b - a))*(((b - a))*(33*((b - a))/256 + 11*((c - b))/32 + 11*((d - c))/64) + ((c - b))*(19*((c - b))/32 + 19*((d - c))/32) + 43*((d - c))^2/128) + ((c - b))*(((c - b))*(3*((c - b))/8 + 9*((d - c))/16) + 25*((d - c))^2/32) + 19*((d - c))^3/64) + ((c - b))*(((c - b))*(((c - b))*(((c - b))/16 + ((d - c))/8) + 11*((d - c))^2/32) + 9*((d - c))^3/32) + 17*((d - c))^4/256 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (17*a^4/256 + a^3*b/64 + a^3*c/64 + a^3*d/64 - 13*a^2*b^2/128 + 3*a^2*b*c/64 + 3*a^2*b*d/64 - 13*a^2*c^2/128 + 3*a^2*c*d/64 - 13*a^2*d^2/128 + a*b^3/64 + 3*a*b^2*c/64 + 3*a*b^2*d/64 + 3*a*b*c^2/64 - 13*a*b*c*d/32 + 3*a*b*d^2/64 + a*c^3/64 + 3*a*c^2*d/64 + 3*a*c*d^2/64 + a*d^3/64 + 17*b^4/256 + b^3*c/64 + b^3*d/64 - 13*b^2*c^2/128 + 3*b^2*c*d/64 - 13*b^2*d^2/128 + b*c^3/64 + 3*b*c^2*d/64 + 3*b*c*d^2/64 + b*d^3/64 + 17*c^4/256 + c^3*d/64 - 13*c^2*d^2/128 + c*d^3/64 + 17*d^4/256) := by
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
  have he : (2*a^2 - a*b*c*d + 2*a*b*c + 2*a*b*d + 2*a*c*d + 2*b^2 + 2*b*c*d + 2*c^2 + 2*d^2 - 15) = (17*a^4/256 + a^3*b/64 + a^3*c/64 + a^3*d/64 - 13*a^2*b^2/128 + 3*a^2*b*c/64 + 3*a^2*b*d/64 - 13*a^2*c^2/128 + 3*a^2*c*d/64 - 13*a^2*d^2/128 + a*b^3/64 + 3*a*b^2*c/64 + 3*a*b^2*d/64 + 3*a*b*c^2/64 - 13*a*b*c*d/32 + 3*a*b*d^2/64 + a*c^3/64 + 3*a*c^2*d/64 + 3*a*c*d^2/64 + a*d^3/64 + 17*b^4/256 + b^3*c/64 + b^3*d/64 - 13*b^2*c^2/128 + 3*b^2*c*d/64 - 13*b^2*d^2/128 + b*c^3/64 + 3*b*c^2*d/64 + 3*b*c*d^2/64 + b*d^3/64 + 17*c^4/256 + c^3*d/64 - 13*c^2*d^2/128 + c*d^3/64 + 17*d^4/256) := by
    linear_combination (-17*a^3/256 + 13*a^2*b/256 + 13*a^2*c/256 + 13*a^2*d/256 - 17*a^2/64 + 13*a*b^2/256 - 19*a*b*c/128 - 19*a*b*d/128 + 15*a*b/32 + 13*a*c^2/256 - 19*a*c*d/128 + 15*a*c/32 + 13*a*d^2/256 + 15*a*d/32 + 15*a/16 - 17*b^3/256 + 13*b^2*c/256 + 13*b^2*d/256 - 17*b^2/64 + 13*b*c^2/256 - 19*b*c*d/128 + 15*b*c/32 + 13*b*d^2/256 + 15*b*d/32 + 15*b/16 - 17*c^3/256 + 13*c^2*d/256 - 17*c^2/64 + 13*c*d^2/256 + 15*c*d/32 + 15*c/16 - 17*d^3/256 - 17*d^2/64 + 15*d/16 + 15/4) * hab
  have hn : 0 ≤ (2*a^2 - a*b*c*d + 2*a*b*c + 2*a*b*d + 2*a*c*d + 2*b^2 + 2*b*c*d + 2*c^2 + 2*d^2 - 15) := by nlinarith only [hp, he]
  have hd : (0 : ℝ) < (2) := by positivity
  have heqrat : ( a^2 + b^2 + c^2 + d^2 + a * b * c + b * c * d + c * d * a + d * a * b ) - ( 1 / 2 * (a * b * c * d + 15)   ) = (2*a^2 - a*b*c*d + 2*a*b*c + 2*a*b*d + 2*a*c*d + 2*b^2 + 2*b*c*d + 2*c^2 + 2*d^2 - 15) / (2) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 4), a^2 + b^2 + c^2 + d^2 + a * b * c + b * c * d + c * d * a + d * a * b ≥ 1 / 2 * (a * b * c * d + 15)) := @solution
#print axioms solution
