-- Prove2me | solution 1 for WorkbookSource.base_44601
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:43:46.905817+00:00
-- url     : https://prove2.me/submissions/11842b11-dc18-4a37-93a5-4d0c34bcc6ef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^5 + b^5 + c^5 + d^5) / (a + b + c + d) ≥ (1/3) * (a^4 + b^4 + c^4 + d^4 - a * b * c * d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (2*a^5 - a^4*b - a^4*c - a^4*d + a^2*b*c*d - a*b^4 + a*b^2*c*d + a*b*c^2*d + a*b*c*d^2 - a*c^4 - a*d^4 + 2*b^5 - b^4*c - b^4*d - b*c^4 - b*d^4 + 2*c^5 - c^4*d - c*d^4 + 2*d^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*(((b - a))*(3*((b - a)) + 4*((c - b)) + 2*((d - c))) + ((c - b))*(4*((c - b)) + 4*((d - c))) + 3*((d - c))^2) + ((b - a))*(((b - a))*(((b - a)) + 2*((c - b)) + ((d - c))) + ((c - b))*(15*((c - b)) + 15*((d - c))) + 14*((d - c))^2) + ((c - b))*(((c - b))*(6*((c - b)) + 9*((d - c))) + 19*((d - c))^2) + 8*((d - c))^3) + ((b - a))*(((b - a))*(((c - b))*(19*((c - b)) + 19*((d - c))) + 19*((d - c))^2) + ((c - b))*(((c - b))*(18*((c - b)) + 27*((d - c))) + 49*((d - c))^2) + 20*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(6*((c - b)) + 12*((d - c))) + 30*((d - c))^2) + 24*((d - c))^3) + 7*((d - c))^4) + ((b - a))*(((b - a))*(((b - a))*(((c - b))*(8*((c - b)) + 8*((d - c))) + 8*((d - c))^2) + ((c - b))*(((c - b))*(12*((c - b)) + 18*((d - c))) + 30*((d - c))^2) + 12*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(8*((c - b)) + 16*((d - c))) + 36*((d - c))^2) + 28*((d - c))^3) + 8*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(2*((c - b)) + 5*((d - c))) + 14*((d - c))^2) + 16*((d - c))^3) + 9*((d - c))^4) + 2*((d - c))^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 - a^4*b - a^4*c - a^4*d + a^2*b*c*d - a*b^4 + a*b^2*c*d + a*b*c^2*d + a*b*c*d^2 - a*c^4 - a*d^4 + 2*b^5 - b^4*c - b^4*d - b*c^4 - b*d^4 + 2*c^5 - c^4*d - c*d^4 + 2*d^5) := by
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
  have hn : 0 ≤ (2*a^5 - a^4*b - a^4*c - a^4*d + a^2*b*c*d - a*b^4 + a*b^2*c*d + a*b*c^2*d + a*b*c*d^2 - a*c^4 - a*d^4 + 2*b^5 - b^4*c - b^4*d - b*c^4 - b*d^4 + 2*c^5 - c^4*d - c*d^4 + 2*d^5) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (3*a + 3*b + 3*c + 3*d) := by positivity
  have heqrat : ( (a^5 + b^5 + c^5 + d^5) / (a + b + c + d) ) - ( (1/3) * (a^4 + b^4 + c^4 + d^4 - a * b * c * d)  ) = (2*a^5 - a^4*b - a^4*c - a^4*d + a^2*b*c*d - a*b^4 + a*b^2*c*d + a*b*c^2*d + a*b*c*d^2 - a*c^4 - a*d^4 + 2*b^5 - b^4*c - b^4*d - b*c^4 - b*d^4 + 2*c^5 - c^4*d - c*d^4 + 2*d^5) / (3*a + 3*b + 3*c + 3*d) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^5 + b^5 + c^5 + d^5) / (a + b + c + d) ≥ (1/3) * (a^4 + b^4 + c^4 + d^4 - a * b * c * d)) := @solution
#print axioms solution
