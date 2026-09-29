-- Prove2me | solution 1 for WorkbookSource.base_22008
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:44:24.900706+00:00
-- url     : https://prove2.me/submissions/e69a355d-3416-40fc-84f8-e0372c63352e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mIndependent0 (gap0 gap1 gap2 gap3 : ℝ) (hg0 : 0 ≤ gap0) (hg1 : 0 ≤ gap1) (hg2 : 0 ≤ gap2) (hg3 : 0 ≤ gap3) : 0 ≤ (2*(gap0)^5*(gap0 + gap1) + 2*(gap0)^5*(gap0 + gap1 + gap2) + 2*(gap0)^5*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^4*(gap0 + gap1)^2 + 4*(gap0)^4*(gap0 + gap1)*(gap0 + gap1 + gap2) + 4*(gap0)^4*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^4*(gap0 + gap1 + gap2)^2 + 4*(gap0)^4*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + 2*(gap0)^4*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2) - (gap0)^3*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3) - (gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2)^2 - (gap0)^3*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^3*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - (gap0)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0)^2*(gap0 + gap1)^4 - (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2) - (gap0)^2*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2 - 8*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)^3 - 8*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^3 + 2*(gap0)^2*(gap0 + gap1 + gap2)^4 - (gap0)^2*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) - 6*(gap0)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 2*(gap0)^2*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0)*(gap0 + gap1)^5 + 4*(gap0)*(gap0 + gap1)^4*(gap0 + gap1 + gap2) + 4*(gap0)*(gap0 + gap1)^4*(gap0 + gap1 + gap2 + gap3) - (gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2)^2 - (gap0)*(gap0 + gap1)^3*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^3 - 8*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - 8*(gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^4 - 8*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 + 4*(gap0)*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0)*(gap0 + gap1 + gap2)^5 + 4*(gap0)*(gap0 + gap1 + gap2)^4*(gap0 + gap1 + gap2 + gap3) - (gap0)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 - (gap0)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0)*(gap0 + gap1 + gap2 + gap3)^5 + 2*(gap0 + gap1)^5*(gap0 + gap1 + gap2) + 2*(gap0 + gap1)^5*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)^4*(gap0 + gap1 + gap2)^2 + 4*(gap0 + gap1)^4*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1)^4*(gap0 + gap1 + gap2 + gap3)^2 - (gap0 + gap1)^3*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3) - (gap0 + gap1)^3*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^4 - (gap0 + gap1)^2*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3) - 6*(gap0 + gap1)^2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^2 - (gap0 + gap1)^2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^3 + 2*(gap0 + gap1)^2*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1)*(gap0 + gap1 + gap2)^5 + 4*(gap0 + gap1)*(gap0 + gap1 + gap2)^4*(gap0 + gap1 + gap2 + gap3) - (gap0 + gap1)*(gap0 + gap1 + gap2)^3*(gap0 + gap1 + gap2 + gap3)^2 - (gap0 + gap1)*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^3 + 4*(gap0 + gap1)*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1)*(gap0 + gap1 + gap2 + gap3)^5 + 2*(gap0 + gap1 + gap2)^5*(gap0 + gap1 + gap2 + gap3) + 2*(gap0 + gap1 + gap2)^4*(gap0 + gap1 + gap2 + gap3)^2 + 2*(gap0 + gap1 + gap2)^2*(gap0 + gap1 + gap2 + gap3)^4 + 2*(gap0 + gap1 + gap2)*(gap0 + gap1 + gap2 + gap3)^5) := by
  have hpos : 0 ≤ (((((((108 : ℝ) * gap1^1 + ((144 : ℝ) * gap2^1 + ((72 : ℝ) * gap3^1))) * gap1^1 + (((144 : ℝ) * gap2^1 + ((144 : ℝ) * gap3^1)) * gap2^1 + ((108 : ℝ) * gap3^2))) * gap0^1 + ((((306 : ℝ) * gap1^1 + ((612 : ℝ) * gap2^1 + ((306 : ℝ) * gap3^1))) * gap1^1 + (((720 : ℝ) * gap2^1 + ((720 : ℝ) * gap3^1)) * gap2^1 + ((414 : ℝ) * gap3^2))) * gap1^1 + ((((288 : ℝ) * gap2^1 + ((432 : ℝ) * gap3^1)) * gap2^1 + ((396 : ℝ) * gap3^2)) * gap2^1 + ((126 : ℝ) * gap3^3)))) * gap0^1 + (((((318 : ℝ) * gap1^1 + ((848 : ℝ) * gap2^1 + ((424 : ℝ) * gap3^1))) * gap1^1 + (((1222 : ℝ) * gap2^1 + ((1222 : ℝ) * gap3^1)) * gap2^1 + ((586 : ℝ) * gap3^2))) * gap1^1 + ((((856 : ℝ) * gap2^1 + ((1284 : ℝ) * gap3^1)) * gap2^1 + ((1060 : ℝ) * gap3^2)) * gap2^1 + ((316 : ℝ) * gap3^3))) * gap1^1 + (((((212 : ℝ) * gap2^1 + ((424 : ℝ) * gap3^1)) * gap2^1 + ((466 : ℝ) * gap3^2)) * gap2^1 + ((254 : ℝ) * gap3^3)) * gap2^1 + ((48 : ℝ) * gap3^4)))) * gap0^1 + ((((((144 : ℝ) * gap1^1 + ((480 : ℝ) * gap2^1 + ((240 : ℝ) * gap3^1))) * gap1^1 + (((836 : ℝ) * gap2^1 + ((836 : ℝ) * gap3^1)) * gap2^1 + ((356 : ℝ) * gap3^2))) * gap1^1 + ((((808 : ℝ) * gap2^1 + ((1212 : ℝ) * gap3^1)) * gap2^1 + ((924 : ℝ) * gap3^2)) * gap2^1 + ((260 : ℝ) * gap3^3))) * gap1^1 + (((((382 : ℝ) * gap2^1 + ((764 : ℝ) * gap3^1)) * gap2^1 + ((790 : ℝ) * gap3^2)) * gap2^1 + ((408 : ℝ) * gap3^3)) * gap2^1 + ((74 : ℝ) * gap3^4))) * gap1^1 + ((((((68 : ℝ) * gap2^1 + ((170 : ℝ) * gap3^1)) * gap2^1 + ((216 : ℝ) * gap3^2)) * gap2^1 + ((154 : ℝ) * gap3^3)) * gap2^1 + ((52 : ℝ) * gap3^4)) * gap2^1 + ((6 : ℝ) * gap3^5)))) * gap0^1 + (((((((24 : ℝ) * gap1^1 + ((96 : ℝ) * gap2^1 + ((48 : ℝ) * gap3^1))) * gap1^1 + (((198 : ℝ) * gap2^1 + ((198 : ℝ) * gap3^1)) * gap2^1 + ((78 : ℝ) * gap3^2))) * gap1^1 + ((((242 : ℝ) * gap2^1 + ((363 : ℝ) * gap3^1)) * gap2^1 + ((261 : ℝ) * gap3^2)) * gap2^1 + ((70 : ℝ) * gap3^3))) * gap1^1 + (((((166 : ℝ) * gap2^1 + ((332 : ℝ) * gap3^1)) * gap2^1 + ((327 : ℝ) * gap3^2)) * gap2^1 + ((161 : ℝ) * gap3^3)) * gap2^1 + ((28 : ℝ) * gap3^4))) * gap1^1 + ((((((58 : ℝ) * gap2^1 + ((145 : ℝ) * gap3^1)) * gap2^1 + ((176 : ℝ) * gap3^2)) * gap2^1 + ((119 : ℝ) * gap3^3)) * gap2^1 + ((38 : ℝ) * gap3^4)) * gap2^1 + ((4 : ℝ) * gap3^5))) * gap1^1 + (((((((8 : ℝ) * gap2^1 + ((24 : ℝ) * gap3^1)) * gap2^1 + ((34 : ℝ) * gap3^2)) * gap2^1 + ((28 : ℝ) * gap3^3)) * gap2^1 + ((12 : ℝ) * gap3^4)) * gap2^1 + ((2 : ℝ) * gap3^5)) * gap2^1))) := by positivity
  convert hpos using 1 <;> ring
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥ a^2 + b^2 + c^2 + d^2  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^5*d + 2*a^4*b^2 + 4*a^4*b*c + 4*a^4*b*d + 2*a^4*c^2 + 4*a^4*c*d + 2*a^4*d^2 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 - a^3*c^2*d - a^3*c*d^2 + 2*a^2*b^4 - a^2*b^3*c - a^2*b^3*d - 6*a^2*b^2*c^2 - 8*a^2*b^2*c*d - 6*a^2*b^2*d^2 - a^2*b*c^3 - 8*a^2*b*c^2*d - 8*a^2*b*c*d^2 - a^2*b*d^3 + 2*a^2*c^4 - a^2*c^3*d - 6*a^2*c^2*d^2 - a^2*c*d^3 + 2*a^2*d^4 + 2*a*b^5 + 4*a*b^4*c + 4*a*b^4*d - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 - 8*a*b^2*c^2*d - 8*a*b^2*c*d^2 - a*b^2*d^3 + 4*a*b*c^4 - 8*a*b*c^2*d^2 + 4*a*b*d^4 + 2*a*c^5 + 4*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 4*a*c*d^4 + 2*a*d^5 + 2*b^5*c + 2*b^5*d + 2*b^4*c^2 + 4*b^4*c*d + 2*b^4*d^2 - b^3*c^2*d - b^3*c*d^2 + 2*b^2*c^4 - b^2*c^3*d - 6*b^2*c^2*d^2 - b^2*c*d^3 + 2*b^2*d^4 + 2*b*c^5 + 4*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 4*b*c*d^4 + 2*b*d^5 + 2*c^5*d + 2*c^4*d^2 + 2*c^2*d^4 + 2*c*d^5) := by
    have hd1 : 0 ≤ b - a := by linarith only [hord1]
    have hd2 : 0 ≤ c - b := by linarith only [hord2]
    have hd3 : 0 ≤ d - c := by linarith only [hord3]
    have hi := p2mIndependent0 a (b - a) (c - b) (d - c) hlow hd1 hd2 hd3
    convert hi using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^5*d + 2*a^4*b^2 + 4*a^4*b*c + 4*a^4*b*d + 2*a^4*c^2 + 4*a^4*c*d + 2*a^4*d^2 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 - a^3*c^2*d - a^3*c*d^2 + 2*a^2*b^4 - a^2*b^3*c - a^2*b^3*d - 6*a^2*b^2*c^2 - 8*a^2*b^2*c*d - 6*a^2*b^2*d^2 - a^2*b*c^3 - 8*a^2*b*c^2*d - 8*a^2*b*c*d^2 - a^2*b*d^3 + 2*a^2*c^4 - a^2*c^3*d - 6*a^2*c^2*d^2 - a^2*c*d^3 + 2*a^2*d^4 + 2*a*b^5 + 4*a*b^4*c + 4*a*b^4*d - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 - 8*a*b^2*c^2*d - 8*a*b^2*c*d^2 - a*b^2*d^3 + 4*a*b*c^4 - 8*a*b*c^2*d^2 + 4*a*b*d^4 + 2*a*c^5 + 4*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 4*a*c*d^4 + 2*a*d^5 + 2*b^5*c + 2*b^5*d + 2*b^4*c^2 + 4*b^4*c*d + 2*b^4*d^2 - b^3*c^2*d - b^3*c*d^2 + 2*b^2*c^4 - b^2*c^3*d - 6*b^2*c^2*d^2 - b^2*c*d^3 + 2*b^2*d^4 + 2*b*c^5 + 4*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 4*b*c*d^4 + 2*b*d^5 + 2*c^5*d + 2*c^4*d^2 + 2*c^2*d^4 + 2*c*d^5) := by
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
  have hn : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^5*d + 2*a^4*b^2 + 4*a^4*b*c + 4*a^4*b*d + 2*a^4*c^2 + 4*a^4*c*d + 2*a^4*d^2 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 - a^3*c^2*d - a^3*c*d^2 + 2*a^2*b^4 - a^2*b^3*c - a^2*b^3*d - 6*a^2*b^2*c^2 - 8*a^2*b^2*c*d - 6*a^2*b^2*d^2 - a^2*b*c^3 - 8*a^2*b*c^2*d - 8*a^2*b*c*d^2 - a^2*b*d^3 + 2*a^2*c^4 - a^2*c^3*d - 6*a^2*c^2*d^2 - a^2*c*d^3 + 2*a^2*d^4 + 2*a*b^5 + 4*a*b^4*c + 4*a*b^4*d - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 - 8*a*b^2*c^2*d - 8*a*b^2*c*d^2 - a*b^2*d^3 + 4*a*b*c^4 - 8*a*b*c^2*d^2 + 4*a*b*d^4 + 2*a*c^5 + 4*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 4*a*c*d^4 + 2*a*d^5 + 2*b^5*c + 2*b^5*d + 2*b^4*c^2 + 4*b^4*c*d + 2*b^4*d^2 - b^3*c^2*d - b^3*c*d^2 + 2*b^2*c^4 - b^2*c^3*d - 6*b^2*c^2*d^2 - b^2*c*d^3 + 2*b^2*d^4 + 2*b*c^5 + 4*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 4*b*c*d^4 + 2*b*d^5 + 2*c^5*d + 2*c^4*d^2 + 2*c^2*d^4 + 2*c*d^5) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by positivity
  have heqrat : ( (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ) - ( a^2 + b^2 + c^2 + d^2  ) = (2*a^5*b + 2*a^5*c + 2*a^5*d + 2*a^4*b^2 + 4*a^4*b*c + 4*a^4*b*d + 2*a^4*c^2 + 4*a^4*c*d + 2*a^4*d^2 - a^3*b^2*c - a^3*b^2*d - a^3*b*c^2 - a^3*b*d^2 - a^3*c^2*d - a^3*c*d^2 + 2*a^2*b^4 - a^2*b^3*c - a^2*b^3*d - 6*a^2*b^2*c^2 - 8*a^2*b^2*c*d - 6*a^2*b^2*d^2 - a^2*b*c^3 - 8*a^2*b*c^2*d - 8*a^2*b*c*d^2 - a^2*b*d^3 + 2*a^2*c^4 - a^2*c^3*d - 6*a^2*c^2*d^2 - a^2*c*d^3 + 2*a^2*d^4 + 2*a*b^5 + 4*a*b^4*c + 4*a*b^4*d - a*b^3*c^2 - a*b^3*d^2 - a*b^2*c^3 - 8*a*b^2*c^2*d - 8*a*b^2*c*d^2 - a*b^2*d^3 + 4*a*b*c^4 - 8*a*b*c^2*d^2 + 4*a*b*d^4 + 2*a*c^5 + 4*a*c^4*d - a*c^3*d^2 - a*c^2*d^3 + 4*a*c*d^4 + 2*a*d^5 + 2*b^5*c + 2*b^5*d + 2*b^4*c^2 + 4*b^4*c*d + 2*b^4*d^2 - b^3*c^2*d - b^3*c*d^2 + 2*b^2*c^4 - b^2*c^3*d - 6*b^2*c^2*d^2 - b^2*c*d^3 + 2*b^2*d^4 + 2*b*c^5 + 4*b*c^4*d - b*c^3*d^2 - b*c^2*d^3 + 4*b*c*d^4 + 2*b*d^5 + 2*c^5*d + 2*c^4*d^2 + 2*c^2*d^4 + 2*c*d^5) / ((a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥ a^2 + b^2 + c^2 + d^2) := @solution
#print axioms solution
