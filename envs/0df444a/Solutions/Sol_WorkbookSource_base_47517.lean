-- Prove2me | solution 1 for WorkbookSource.base_47517
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:12:33.89875+00:00
-- url     : https://prove2.me/submissions/83043c0f-ac64-417f-aca0-b791ae039421

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (d^3 - a * b * c) / (a + b + c) + (a^3 - b * c * d) / (b + c + d) + (b^3 - a * c * d) / (a + c + d) + (c^3 - a * b * d) / (d + a + b) ≥ 0  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c + 2*a^5*d + a^4*b^2 + 3*a^4*b*c + 3*a^4*b*d + a^4*c^2 + 3*a^4*c*d + a^4*d^2 - 2*a^3*b*c*d + a^2*b^4 - 2*a^2*b^2*c^2 - 10*a^2*b^2*c*d - 2*a^2*b^2*d^2 - 10*a^2*b*c^2*d - 10*a^2*b*c*d^2 + a^2*c^4 - 2*a^2*c^2*d^2 + a^2*d^4 + 2*a*b^5 + 3*a*b^4*c + 3*a*b^4*d - 2*a*b^3*c*d - 10*a*b^2*c^2*d - 10*a*b^2*c*d^2 + 3*a*b*c^4 - 2*a*b*c^3*d - 10*a*b*c^2*d^2 - 2*a*b*c*d^3 + 3*a*b*d^4 + 2*a*c^5 + 3*a*c^4*d + 3*a*c*d^4 + 2*a*d^5 + b^6 + 2*b^5*c + 2*b^5*d + b^4*c^2 + 3*b^4*c*d + b^4*d^2 + b^2*c^4 - 2*b^2*c^2*d^2 + b^2*d^4 + 2*b*c^5 + 3*b*c^4*d + 3*b*c*d^4 + 2*b*d^5 + c^6 + 2*c^5*d + c^4*d^2 + c^2*d^4 + 2*c*d^5 + d^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*((a)*((a)*(((b - a))*(108*((b - a)) + 144*((c - b)) + 72*((d - c))) + ((c - b))*(144*((c - b)) + 144*((d - c))) + 108*((d - c))^2) + ((b - a))*(((b - a))*(306*((b - a)) + 612*((c - b)) + 306*((d - c))) + ((c - b))*(720*((c - b)) + 720*((d - c))) + 414*((d - c))^2) + ((c - b))*(((c - b))*(288*((c - b)) + 432*((d - c))) + 396*((d - c))^2) + 126*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(327*((b - a)) + 872*((c - b)) + 436*((d - c))) + ((c - b))*(1246*((c - b)) + 1246*((d - c))) + 592*((d - c))^2) + ((c - b))*(((c - b))*(856*((c - b)) + 1284*((d - c))) + 1084*((d - c))^2) + 328*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(212*((c - b)) + 424*((d - c))) + 490*((d - c))^2) + 278*((d - c))^3) + 57*((d - c))^4) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(156*((b - a)) + 520*((c - b)) + 260*((d - c))) + ((c - b))*(890*((c - b)) + 890*((d - c))) + 370*((d - c))^2) + ((c - b))*(((c - b))*(828*((c - b)) + 1242*((d - c))) + 978*((d - c))^2) + 282*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(382*((c - b)) + 764*((d - c))) + 856*((d - c))^2) + 474*((d - c))^3) + 96*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(68*((c - b)) + 170*((d - c))) + 244*((d - c))^2) + 196*((d - c))^3) + 78*((d - c))^4) + 12*((d - c))^5) + ((b - a))*(((b - a))*(((b - a))*(((b - a))*(((b - a))*(28*((b - a)) + 112*((c - b)) + 56*((d - c))) + ((c - b))*(225*((c - b)) + 225*((d - c))) + 85*((d - c))^2) + ((c - b))*(((c - b))*(260*((c - b)) + 390*((d - c))) + 290*((d - c))^2) + 80*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(170*((c - b)) + 340*((d - c))) + 370*((d - c))^2) + 200*((d - c))^3) + 40*((d - c))^4) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(58*((c - b)) + 145*((d - c))) + 206*((d - c))^2) + 164*((d - c))^3) + 65*((d - c))^4) + 10*((d - c))^5) + ((c - b))*(((c - b))*(((c - b))*(((c - b))*(((c - b))*(8*((c - b)) + 24*((d - c))) + 42*((d - c))^2) + 44*((d - c))^3) + 26*((d - c))^4) + 8*((d - c))^5) + ((d - c))^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c + 2*a^5*d + a^4*b^2 + 3*a^4*b*c + 3*a^4*b*d + a^4*c^2 + 3*a^4*c*d + a^4*d^2 - 2*a^3*b*c*d + a^2*b^4 - 2*a^2*b^2*c^2 - 10*a^2*b^2*c*d - 2*a^2*b^2*d^2 - 10*a^2*b*c^2*d - 10*a^2*b*c*d^2 + a^2*c^4 - 2*a^2*c^2*d^2 + a^2*d^4 + 2*a*b^5 + 3*a*b^4*c + 3*a*b^4*d - 2*a*b^3*c*d - 10*a*b^2*c^2*d - 10*a*b^2*c*d^2 + 3*a*b*c^4 - 2*a*b*c^3*d - 10*a*b*c^2*d^2 - 2*a*b*c*d^3 + 3*a*b*d^4 + 2*a*c^5 + 3*a*c^4*d + 3*a*c*d^4 + 2*a*d^5 + b^6 + 2*b^5*c + 2*b^5*d + b^4*c^2 + 3*b^4*c*d + b^4*d^2 + b^2*c^4 - 2*b^2*c^2*d^2 + b^2*d^4 + 2*b*c^5 + 3*b*c^4*d + 3*b*c*d^4 + 2*b*d^5 + c^6 + 2*c^5*d + c^4*d^2 + c^2*d^4 + 2*c*d^5 + d^6) := by
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
  have hn : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c + 2*a^5*d + a^4*b^2 + 3*a^4*b*c + 3*a^4*b*d + a^4*c^2 + 3*a^4*c*d + a^4*d^2 - 2*a^3*b*c*d + a^2*b^4 - 2*a^2*b^2*c^2 - 10*a^2*b^2*c*d - 2*a^2*b^2*d^2 - 10*a^2*b*c^2*d - 10*a^2*b*c*d^2 + a^2*c^4 - 2*a^2*c^2*d^2 + a^2*d^4 + 2*a*b^5 + 3*a*b^4*c + 3*a*b^4*d - 2*a*b^3*c*d - 10*a*b^2*c^2*d - 10*a*b^2*c*d^2 + 3*a*b*c^4 - 2*a*b*c^3*d - 10*a*b*c^2*d^2 - 2*a*b*c*d^3 + 3*a*b*d^4 + 2*a*c^5 + 3*a*c^4*d + 3*a*c*d^4 + 2*a*d^5 + b^6 + 2*b^5*c + 2*b^5*d + b^4*c^2 + 3*b^4*c*d + b^4*d^2 + b^2*c^4 - 2*b^2*c^2*d^2 + b^2*d^4 + 2*b*c^5 + 3*b*c^4*d + 3*b*c*d^4 + 2*b*d^5 + c^6 + 2*c^5*d + c^4*d^2 + c^2*d^4 + 2*c*d^5 + d^6) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by positivity
  have heqrat : ( (d^3 - a * b * c) / (a + b + c) + (a^3 - b * c * d) / (b + c + d) + (b^3 - a * c * d) / (a + c + d) + (c^3 - a * b * d) / (d + a + b) ) - ( 0  ) = (a^6 + 2*a^5*b + 2*a^5*c + 2*a^5*d + a^4*b^2 + 3*a^4*b*c + 3*a^4*b*d + a^4*c^2 + 3*a^4*c*d + a^4*d^2 - 2*a^3*b*c*d + a^2*b^4 - 2*a^2*b^2*c^2 - 10*a^2*b^2*c*d - 2*a^2*b^2*d^2 - 10*a^2*b*c^2*d - 10*a^2*b*c*d^2 + a^2*c^4 - 2*a^2*c^2*d^2 + a^2*d^4 + 2*a*b^5 + 3*a*b^4*c + 3*a*b^4*d - 2*a*b^3*c*d - 10*a*b^2*c^2*d - 10*a*b^2*c*d^2 + 3*a*b*c^4 - 2*a*b*c^3*d - 10*a*b*c^2*d^2 - 2*a*b*c*d^3 + 3*a*b*d^4 + 2*a*c^5 + 3*a*c^4*d + 3*a*c*d^4 + 2*a*d^5 + b^6 + 2*b^5*c + 2*b^5*d + b^4*c^2 + 3*b^4*c*d + b^4*d^2 + b^2*c^4 - 2*b^2*c^2*d^2 + b^2*d^4 + 2*b*c^5 + 3*b*c^4*d + 3*b*c*d^4 + 2*b*d^5 + c^6 + 2*c^5*d + c^4*d^2 + c^2*d^4 + 2*c*d^5 + d^6) / ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (d^3 - a * b * c) / (a + b + c) + (a^3 - b * c * d) / (b + c + d) + (b^3 - a * c * d) / (a + c + d) + (c^3 - a * b * d) / (d + a + b) ≥ 0) := @solution
#print axioms solution
