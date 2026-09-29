-- Prove2me | solution 1 for WorkbookSource.base_56382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:28:21.453104+00:00
-- url     : https://prove2.me/submissions/a2b072eb-22d8-4e22-93bc-5fbd092bf785

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma p2mIndependent (x u v : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ (x^15 - x^6*(x+u)^5*(x+u+v)^4 - x^6*(x+u)^4*(x+u+v)^5 - x^5*(x+u)^6*(x+u+v)^4 + 3*x^5*(x+u)^5*(x+u+v)^5 - x^5*(x+u)^4*(x+u+v)^6 - x^4*(x+u)^6*(x+u+v)^5 - x^4*(x+u)^5*(x+u+v)^6 + (x+u)^15 + (x+u+v)^15) := by
  have hpos : 0 ≤ (73 : ℝ) * (x^13 * u^2) + (73 : ℝ) * (x^13 * u^1 * v^1) + (73 : ℝ) * (x^13 * v^2) + (532 : ℝ) * (x^12 * u^3) + (798 : ℝ) * (x^12 * u^2 * v^1) + (1100 : ℝ) * (x^12 * u^1 * v^2) + (417 : ℝ) * (x^12 * v^3) + (2028 : ℝ) * (x^11 * u^4) + (4056 : ℝ) * (x^11 * u^3 * v^1) + (7206 : ℝ) * (x^11 * u^2 * v^2) + (5178 : ℝ) * (x^11 * u^1 * v^3) + (1338 : ℝ) * (x^11 * v^4) + (5082 : ℝ) * (x^10 * u^5) + (12705 : ℝ) * (x^10 * u^4 * v^1) + (27874 : ℝ) * (x^10 * u^3 * v^2) + (29106 : ℝ) * (x^10 * u^2 * v^3) + (14839 : ℝ) * (x^10 * u^1 * v^4) + (2992 : ℝ) * (x^10 * v^5) + (9128 : ℝ) * (x^9 * u^6) + (27384 : ℝ) * (x^9 * u^5 * v^1) + (71995 : ℝ) * (x^9 * u^4 * v^2) + (98350 : ℝ) * (x^9 * u^3 * v^3) + (74580 : ℝ) * (x^9 * u^2 * v^4) + (29969 : ℝ) * (x^9 * u^1 * v^5) + (5003 : ℝ) * (x^9 * v^6) + (12258 : ℝ) * (x^8 * u^7) + (42903 : ℝ) * (x^8 * u^6 * v^1) + (132153 : ℝ) * (x^8 * u^5 * v^2) + (223125 : ℝ) * (x^8 * u^4 * v^3) + (224445 : ℝ) * (x^8 * u^3 * v^4) + (134994 : ℝ) * (x^8 * u^2 * v^5) + (45036 : ℝ) * (x^8 * u^1 * v^6) + (6435 : ℝ) * (x^8 * v^7) + (12567 : ℝ) * (x^7 * u^8) + (50268 : ℝ) * (x^7 * u^7 * v^1) + (178220 : ℝ) * (x^7 * u^6 * v^2) + (358722 : ℝ) * (x^7 * u^5 * v^3) + (449705 : ℝ) * (x^7 * u^4 * v^4) + (360186 : ℝ) * (x^7 * u^3 * v^5) + (180164 : ℝ) * (x^7 * u^2 * v^6) + (51480 : ℝ) * (x^7 * u^1 * v^7) + (6435 : ℝ) * (x^7 * v^8) + (9908 : ℝ) * (x^6 * u^9) + (44586 : ℝ) * (x^6 * u^8 * v^1) + (179336 : ℝ) * (x^6 * u^7 * v^2) + (419608 : ℝ) * (x^6 * u^6 * v^3) + (630198 : ℝ) * (x^6 * u^5 * v^4) + (630509 : ℝ) * (x^6 * u^4 * v^5) + (420406 : ℝ) * (x^6 * u^3 * v^6) + (180180 : ℝ) * (x^6 * u^2 * v^7) + (45045 : ℝ) * (x^6 * u^1 * v^8) + (5005 : ℝ) * (x^6 * v^9) + (5985 : ℝ) * (x^5 * u^10) + (29925 : ℝ) * (x^5 * u^9 * v^1) + (134919 : ℝ) * (x^5 * u^8 * v^2) + (360126 : ℝ) * (x^5 * u^7 * v^3) + (630489 : ℝ) * (x^5 * u^6 * v^4) + (756711 : ℝ) * (x^5 * u^5 * v^5) + (630624 : ℝ) * (x^5 * u^4 * v^6) + (360360 : ℝ) * (x^5 * u^3 * v^7) + (135135 : ℝ) * (x^5 * u^2 * v^8) + (30030 : ℝ) * (x^5 * u^1 * v^9) + (3003 : ℝ) * (x^5 * v^10) + (2728 : ℝ) * (x^4 * u^11) + (15004 : ℝ) * (x^4 * u^10 * v^1) + (75050 : ℝ) * (x^4 * u^9 * v^2) + (225195 : ℝ) * (x^4 * u^8 * v^3) + (450430 : ℝ) * (x^4 * u^7 * v^4) + (630623 : ℝ) * (x^4 * u^6 * v^5) + (630629 : ℝ) * (x^4 * u^5 * v^6) + (450450 : ℝ) * (x^4 * u^4 * v^7) + (225225 : ℝ) * (x^4 * u^3 * v^8) + (75075 : ℝ) * (x^4 * u^2 * v^9) + (15015 : ℝ) * (x^4 * u^1 * v^10) + (1365 : ℝ) * (x^4 * v^11) + (910 : ℝ) * (x^3 * u^12) + (5460 : ℝ) * (x^3 * u^11 * v^1) + (30030 : ℝ) * (x^3 * u^10 * v^2) + (100100 : ℝ) * (x^3 * u^9 * v^3) + (225225 : ℝ) * (x^3 * u^8 * v^4) + (360360 : ℝ) * (x^3 * u^7 * v^5) + (420420 : ℝ) * (x^3 * u^6 * v^6) + (360360 : ℝ) * (x^3 * u^5 * v^7) + (225225 : ℝ) * (x^3 * u^4 * v^8) + (100100 : ℝ) * (x^3 * u^3 * v^9) + (30030 : ℝ) * (x^3 * u^2 * v^10) + (5460 : ℝ) * (x^3 * u^1 * v^11) + (455 : ℝ) * (x^3 * v^12) + (210 : ℝ) * (x^2 * u^13) + (1365 : ℝ) * (x^2 * u^12 * v^1) + (8190 : ℝ) * (x^2 * u^11 * v^2) + (30030 : ℝ) * (x^2 * u^10 * v^3) + (75075 : ℝ) * (x^2 * u^9 * v^4) + (135135 : ℝ) * (x^2 * u^8 * v^5) + (180180 : ℝ) * (x^2 * u^7 * v^6) + (180180 : ℝ) * (x^2 * u^6 * v^7) + (135135 : ℝ) * (x^2 * u^5 * v^8) + (75075 : ℝ) * (x^2 * u^4 * v^9) + (30030 : ℝ) * (x^2 * u^3 * v^10) + (8190 : ℝ) * (x^2 * u^2 * v^11) + (1365 : ℝ) * (x^2 * u^1 * v^12) + (105 : ℝ) * (x^2 * v^13) + (30 : ℝ) * (x^1 * u^14) + (210 : ℝ) * (x^1 * u^13 * v^1) + (1365 : ℝ) * (x^1 * u^12 * v^2) + (5460 : ℝ) * (x^1 * u^11 * v^3) + (15015 : ℝ) * (x^1 * u^10 * v^4) + (30030 : ℝ) * (x^1 * u^9 * v^5) + (45045 : ℝ) * (x^1 * u^8 * v^6) + (51480 : ℝ) * (x^1 * u^7 * v^7) + (45045 : ℝ) * (x^1 * u^6 * v^8) + (30030 : ℝ) * (x^1 * u^5 * v^9) + (15015 : ℝ) * (x^1 * u^4 * v^10) + (5460 : ℝ) * (x^1 * u^3 * v^11) + (1365 : ℝ) * (x^1 * u^2 * v^12) + (210 : ℝ) * (x^1 * u^1 * v^13) + (15 : ℝ) * (x^1 * v^14) + (2 : ℝ) * (u^15) + (15 : ℝ) * (u^14 * v^1) + (105 : ℝ) * (u^13 * v^2) + (455 : ℝ) * (u^12 * v^3) + (1365 : ℝ) * (u^11 * v^4) + (3003 : ℝ) * (u^10 * v^5) + (5005 : ℝ) * (u^9 * v^6) + (6435 : ℝ) * (u^8 * v^7) + (6435 : ℝ) * (u^7 * v^8) + (5005 : ℝ) * (u^6 * v^9) + (3003 : ℝ) * (u^5 * v^10) + (1365 : ℝ) * (u^4 * v^11) + (455 : ℝ) * (u^3 * v^12) + (105 : ℝ) * (u^2 * v^13) + (15 : ℝ) * (u^1 * v^14) + (1 : ℝ) * (v^15) := by positivity
  convert hpos using 1 <;> ring
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 15 + y ^ 15 + z ^ 15 + 3 * x ^ 5 * y ^ 5 * z ^ 5 ≥ x ^ 6 * y ^ 5 * z ^ 4 + x ^ 6 * y ^ 4 * z ^ 5 + x ^ 5 * y ^ 6 * z ^ 4 + x ^ 4 * y ^ 6 * z ^ 5 + x ^ 5 * y ^ 4 * z ^ 6 + x ^ 4 * y ^ 5 * z ^ 6  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^15 - x^6*y^5*z^4 - x^6*y^4*z^5 - x^5*y^6*z^4 + 3*x^5*y^5*z^5 - x^5*y^4*z^6 - x^4*y^6*z^5 - x^4*y^5*z^6 + y^15 + z^15) := by
    have hu : 0 ≤ y-x := by linarith only [hord1]
    have hv : 0 ≤ z-y := by linarith only [hord2]
    have hq := p2mIndependent x (y-x) (z-y) hlow hu hv
    convert hq using 1 <;> ring
  have hp : 0 ≤ (x^15 - x^6*y^5*z^4 - x^6*y^4*z^5 - x^5*y^6*z^4 + 3*x^5*y^5*z^5 - x^5*y^4*z^6 - x^4*y^6*z^5 - x^4*y^5*z^6 + y^15 + z^15) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (x^15 - x^6*y^5*z^4 - x^6*y^4*z^5 - x^5*y^6*z^4 + 3*x^5*y^5*z^5 - x^5*y^4*z^6 - x^4*y^6*z^5 - x^4*y^5*z^6 + y^15 + z^15) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (1) := by positivity
  have heqrat : ( x ^ 15 + y ^ 15 + z ^ 15 + 3 * x ^ 5 * y ^ 5 * z ^ 5 ) - ( x ^ 6 * y ^ 5 * z ^ 4 + x ^ 6 * y ^ 4 * z ^ 5 + x ^ 5 * y ^ 6 * z ^ 4 + x ^ 4 * y ^ 6 * z ^ 5 + x ^ 5 * y ^ 4 * z ^ 6 + x ^ 4 * y ^ 5 * z ^ 6  ) = (x^15 - x^6*y^5*z^4 - x^6*y^4*z^5 - x^5*y^6*z^4 + 3*x^5*y^5*z^5 - x^5*y^4*z^6 - x^4*y^6*z^5 - x^4*y^5*z^6 + y^15 + z^15) / (1) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x ^ 15 + y ^ 15 + z ^ 15 + 3 * x ^ 5 * y ^ 5 * z ^ 5 ≥ x ^ 6 * y ^ 5 * z ^ 4 + x ^ 6 * y ^ 4 * z ^ 5 + x ^ 5 * y ^ 6 * z ^ 4 + x ^ 4 * y ^ 6 * z ^ 5 + x ^ 5 * y ^ 4 * z ^ 6 + x ^ 4 * y ^ 5 * z ^ 6) := @solution
#print axioms solution
