-- Prove2me | solution 1 for WorkbookSource.plus_70121
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:00:47.123883+00:00
-- url     : https://prove2.me/submissions/55a8ab37-7541-457e-8bc4-4cf2b83f842c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b + b * c + c * d + d * a + a * c + b * d) * (a * b * c + b * c * d + c * d * a + d * a * b) / (a + b + c + d) + 3 * (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / (a + b + c + d) ^ 2 ≥ 9 * a * b * c * d   := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 6*a^2*b^2*c^2 - 4*a^2*b^2*c*d + 6*a^2*b^2*d^2 + a^2*b*c^3 - 4*a^2*b*c^2*d - 4*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 6*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 4*a*b^2*c^2*d - 4*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 4*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 6*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*((a)*(((b - a))*(12*((b - a)) + 16*((c - b)) + 8*((d - c))) + ((c - b))*(16*((c - b)) + 16*((d - c))) + 12*((d - c))^2) + ((b - a))*(((b - a))*(48*((b - a)) + 96*((c - b)) + 48*((d - c))) + ((c - b))*(80*((c - b)) + 80*((d - c))) + 32*((d - c))^2) + ((c - b))*(((c - b))*(32*((c - b)) + 48*((d - c))) + 16*((d - c))^2)) + ((b - a))*(((b - a))*(((b - a))*(72*((b - a)) + 192*((c - b)) + 96*((d - c))) + ((c - b))*(188*((c - b)) + 188*((d - c))) + 44*((d - c))^2) + ((c - b))*(((c - b))*(88*((c - b)) + 132*((d - c))) + 44*((d - c))^2)) + ((c - b))^2*(((c - b))*(20*((c - b)) + 40*((d - c))) + 20*((d - c))^2)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(48*((b - a)) + 160*((c - b)) + 80*((d - c))) + ((c - b))*(198*((c - b)) + 198*((d - c))) + 38*((d - c))^2) + ((c - b))*(((c - b))*(112*((c - b)) + 168*((d - c))) + 60*((d - c))^2) + 2*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(30*((c - b)) + 60*((d - c))) + 32*((d - c))^2) + 2*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(4*((c - b)) + 10*((d - c))) + 8*((d - c))^2) + 2*((d - c))^3)) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((b - a))*(12*((b - a)) + 48*((c - b)) + 24*((d - c))) + ((c - b))*(74*((c - b)) + 74*((d - c))) + 14*((d - c))^2) + ((c - b))*(((c - b))*(54*((c - b)) + 81*((d - c))) + 31*((d - c))^2) + 2*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(18*((c - b)) + 36*((d - c))) + 21*((d - c))^2) + 3*((d - c))^3)) + ((c - b))^2*(((c - b))*(((c - b))*(2*((c - b)) + 5*((d - c))) + 4*((d - c))^2) + ((d - c))^3)) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 6*a^2*b^2*c^2 - 4*a^2*b^2*c*d + 6*a^2*b^2*d^2 + a^2*b*c^3 - 4*a^2*b*c^2*d - 4*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 6*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 4*a*b^2*c^2*d - 4*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 4*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 6*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by
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
  have hn : 0 ≤ (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 6*a^2*b^2*c^2 - 4*a^2*b^2*c*d + 6*a^2*b^2*d^2 + a^2*b*c^3 - 4*a^2*b*c^2*d - 4*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 6*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 4*a*b^2*c^2*d - 4*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 4*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 6*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + c + d)^2) := by positivity
  have heqrat : ( (a * b + b * c + c * d + d * a + a * c + b * d) * (a * b * c + b * c * d + c * d * a + d * a * b) / (a + b + c + d) + 3 * (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / (a + b + c + d) ^ 2 ) - ( 9 * a * b * c * d   ) = (a^3*b^2*c + a^3*b^2*d + a^3*b*c^2 - 6*a^3*b*c*d + a^3*b*d^2 + a^3*c^2*d + a^3*c*d^2 + a^2*b^3*c + a^2*b^3*d + 6*a^2*b^2*c^2 - 4*a^2*b^2*c*d + 6*a^2*b^2*d^2 + a^2*b*c^3 - 4*a^2*b*c^2*d - 4*a^2*b*c*d^2 + a^2*b*d^3 + a^2*c^3*d + 6*a^2*c^2*d^2 + a^2*c*d^3 + a*b^3*c^2 - 6*a*b^3*c*d + a*b^3*d^2 + a*b^2*c^3 - 4*a*b^2*c^2*d - 4*a*b^2*c*d^2 + a*b^2*d^3 - 6*a*b*c^3*d - 4*a*b*c^2*d^2 - 6*a*b*c*d^3 + a*c^3*d^2 + a*c^2*d^3 + b^3*c^2*d + b^3*c*d^2 + b^2*c^3*d + 6*b^2*c^2*d^2 + b^2*c*d^3 + b*c^3*d^2 + b*c^2*d^3) / ((a + b + c + d)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a * b + b * c + c * d + d * a + a * c + b * d) * (a * b * c + b * c * d + c * d * a + d * a * b) / (a + b + c + d) + 3 * (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / (a + b + c + d) ^ 2 ≥ 9 * a * b * c * d) := @solution
#print axioms solution
