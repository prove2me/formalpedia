-- Prove2me | solution 1 for YieldPostpone.Interplay.interaction_mid_cDR1_pos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T02:41:08.974692+00:00
-- url     : https://prove2.me/submissions/c15d6b1a-350d-4eac-9ff9-1e17b8d630b7

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YP3Alg

noncomputable def P0p (α θ : ℝ) : ℝ :=
  -α^8*θ^9 + 7*α^8*θ^8 - 21*α^8*θ^7 + 35*α^8*θ^6 - 35*α^8*θ^5 + 21*α^8*θ^4 - 7*α^8*θ^3 + α^8*θ^2 - α^7*θ^9 + 3*α^7*θ^8 + 7*α^7*θ^7 - 45*α^7*θ^6 + 85*α^7*θ^5 - 79*α^7*θ^4 + 37*α^7*θ^3 - 7*α^7*θ^2 + 11*α^6*θ^9 - 55*α^6*θ^8 + 111*α^6*θ^7 - 119*α^6*θ^6 + 81*α^6*θ^5 - 45*α^6*θ^4 + 21*α^6*θ^3 - 5*α^6*θ^2 - 9*α^5*θ^9 + 57*α^5*θ^8 - 217*α^5*θ^7 + 489*α^5*θ^6 - 611*α^5*θ^5 + 403*α^5*θ^4 - 123*α^5*θ^3 + 11*α^5*θ^2 - 15*α^4*θ^9 + 21*α^4*θ^8 + 244*α^4*θ^7 - 794*α^4*θ^6 + 933*α^4*θ^5 - 475*α^4*θ^4 + 86*α^4*θ^3 + 21*α^3*θ^9 - 51*α^3*θ^8 - 200*α^3*θ^7 + 646*α^3*θ^6 - 607*α^3*θ^5 + 205*α^3*θ^4 - 14*α^3*θ^3 + α^2*θ^9 + 23*α^2*θ^8 + 82*α^2*θ^7 - 250*α^2*θ^6 + 173*α^2*θ^5 - 29*α^2*θ^4 - 11*α*θ^9 - 9*α*θ^8 - 2*α*θ^7 + 42*α*θ^6 - 19*α*θ^5 - α*θ^4 + 4*θ^9 + 4*θ^8 - 4*θ^7 - 4*θ^6

noncomputable def P1p (α θ : ℝ) : ℝ :=
  4*α^6*θ^7 - 20*α^6*θ^6 + 40*α^6*θ^5 - 40*α^6*θ^4 + 20*α^6*θ^3 - 4*α^6*θ^2 + 8*α^5*θ^7 - 32*α^5*θ^6 + 48*α^5*θ^5 - 32*α^5*θ^4 + 8*α^5*θ^3 - 56*α^4*θ^7 + 212*α^4*θ^6 - 312*α^4*θ^5 + 224*α^4*θ^4 - 80*α^4*θ^3 + 12*α^4*θ^2 + 56*α^3*θ^7 - 232*α^3*θ^6 + 376*α^3*θ^5 - 280*α^3*θ^4 + 80*α^3*θ^3 + 28*α^2*θ^7 + 72*α^2*θ^6 - 240*α^2*θ^5 + 152*α^2*θ^4 - 12*α^2*θ^3 - 64*α*θ^7 - 16*α*θ^6 + 96*α*θ^5 - 16*α*θ^4 + 24*θ^7 + 16*θ^6 - 8*θ^5

noncomputable def qp (α θ : ℝ) : ℝ :=
  -4*α^4*θ^5 + 12*α^4*θ^4 - 12*α^4*θ^3 + 4*α^4*θ^2 - 4*α^3*θ^6 + 4*α^3*θ^5 + 12*α^3*θ^4 - 20*α^3*θ^3 + 8*α^3*θ^2 + 4*α^2*θ^6 + 36*α^2*θ^5 - 84*α^2*θ^4 + 44*α^2*θ^3 + 4*α*θ^6 - 60*α*θ^5 + 60*α*θ^4 - 4*α*θ^3 - 4*θ^6 + 24*θ^5 - 4*θ^4

noncomputable def Rp (α θ : ℝ) : ℝ :=
  -4*α^8*θ^6 + 24*α^8*θ^5 - 60*α^8*θ^4 + 80*α^8*θ^3 - 60*α^8*θ^2 + 24*α^8*θ - 4*α^8 - 5*α^7*θ^6 + 26*α^7*θ^5 - 55*α^7*θ^4 + 60*α^7*θ^3 - 35*α^7*θ^2 + 10*α^7*θ - α^7 + 62*α^6*θ^6 - 292*α^6*θ^5 + 566*α^6*θ^4 - 584*α^6*θ^3 + 346*α^6*θ^2 - 116*α^6*θ + 18*α^6 - 103*α^5*θ^6 + 464*α^5*θ^5 - 859*α^5*θ^4 + 812*α^5*θ^3 - 377*α^5*θ^2 + 52*α^5*θ + 11*α^5 + 28*α^4*θ^6 - 264*α^4*θ^5 + 580*α^4*θ^4 - 420*α^4*θ^3 + 16*α^4*θ^2 + 60*α^4*θ + 77*α^3*θ^6 + 42*α^3*θ^5 - 210*α^3*θ^4 - 28*α^3*θ^3 + 133*α^3*θ^2 - 14*α^3*θ - 82*α^2*θ^6 - 20*α^2*θ^5 + 32*α^2*θ^4 + 100*α^2*θ^3 - 30*α^2*θ^2 + 31*α*θ^6 + 28*α*θ^5 + 10*α*θ^4 - 20*α*θ^3 - α*θ^2 - 4*θ^6 - 8*θ^5 - 4*θ^4

noncomputable def P1rp (α θ : ℝ) : ℝ :=
  α^6*θ^5 - 5*α^6*θ^4 + 10*α^6*θ^3 - 10*α^6*θ^2 + 5*α^6*θ - α^6 + 2*α^5*θ^5 - 8*α^5*θ^4 + 12*α^5*θ^3 - 8*α^5*θ^2 + 2*α^5*θ - 14*α^4*θ^5 + 53*α^4*θ^4 - 78*α^4*θ^3 + 56*α^4*θ^2 - 20*α^4*θ + 3*α^4 + 14*α^3*θ^5 - 58*α^3*θ^4 + 94*α^3*θ^3 - 70*α^3*θ^2 + 20*α^3*θ + 7*α^2*θ^5 + 18*α^2*θ^4 - 60*α^2*θ^3 + 38*α^2*θ^2 - 3*α^2*θ - 16*α*θ^5 - 4*α*θ^4 + 24*α*θ^3 - 4*α*θ^2 + 6*θ^5 + 4*θ^4 - 2*θ^3


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
lemma R_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < Rp α θ := by
  unfold Rp
  have hp : (0:ℝ) ≤ 16*α-9 := by linarith
  have hq : (0:ℝ) ≤ 16-16*α := by linarith
  have ha : (0:ℝ) ≤ θ := h3.le
  have hb : (0:ℝ) ≤ 1-θ := by linarith
  have c0 : (0:ℝ) ≤ -4*α^8 - α^7 + 18*α^6 + 11*α^5 - 1 := by
    have h : (0:ℝ) ≤ 141427547 * (16*α-9)^0 * (16-16*α)^8 + 6203047132 * (16*α-9)^1 * (16-16*α)^7 + 48068119232 * (16*α-9)^2 * (16-16*α)^6 + 173505955840 * (16*α-9)^3 * (16-16*α)^5 + 356944609280 * (16*α-9)^4 * (16-16*α)^4 + 445328916480 * (16*α-9)^5 * (16-16*α)^3 + 334499938304 * (16*α-9)^6 * (16-16*α)^2 + 139318001664 * (16*α-9)^7 * (16-16*α)^1 + 24696061952 * (16*α-9)^8 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 8)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 7))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 6))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 5))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 6)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 7)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 8)) (pow_nonneg hq 0)))
    have e : (6189907940737024:ℝ) * ((-4*α^8 - α^7 + 18*α^6 + 11*α^5) - 1) = 141427547 * (16*α-9)^0 * (16-16*α)^8 + 6203047132 * (16*α-9)^1 * (16-16*α)^7 + 48068119232 * (16*α-9)^2 * (16-16*α)^6 + 173505955840 * (16*α-9)^3 * (16-16*α)^5 + 356944609280 * (16*α-9)^4 * (16-16*α)^4 + 445328916480 * (16*α-9)^5 * (16-16*α)^3 + 334499938304 * (16*α-9)^6 * (16-16*α)^2 + 139318001664 * (16*α-9)^7 * (16-16*α)^1 + 24696061952 * (16*α-9)^8 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c1 : (0:ℝ) ≤ 2*α^7/3 - 4*α^6/3 + 59*α^5/3 + 10*α^4 - 7*α^3/3 - 1 := by
    have h : (0:ℝ) ≤ 266954457 * (16*α-9)^0 * (16-16*α)^7 + 4413508176 * (16*α-9)^1 * (16-16*α)^6 + 24638769792 * (16*α-9)^2 * (16-16*α)^5 + 69031524352 * (16*α-9)^3 * (16-16*α)^4 + 109596540928 * (16*α-9)^4 * (16-16*α)^3 + 100518068224 * (16*α-9)^5 * (16-16*α)^2 + 49794777088 * (16*α-9)^6 * (16-16*α)^1 + 10334765056 * (16*α-9)^7 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 7)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 6))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 5))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 6)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 7)) (pow_nonneg hq 0)))
    have e : (331602211110912:ℝ) * ((2*α^7/3 - 4*α^6/3 + 59*α^5/3 + 10*α^4 - 7*α^3/3) - 1) = 266954457 * (16*α-9)^0 * (16-16*α)^7 + 4413508176 * (16*α-9)^1 * (16-16*α)^6 + 24638769792 * (16*α-9)^2 * (16-16*α)^5 + 69031524352 * (16*α-9)^3 * (16-16*α)^4 + 109596540928 * (16*α-9)^4 * (16-16*α)^3 + 100518068224 * (16*α-9)^5 * (16-16*α)^2 + 49794777088 * (16*α-9)^6 * (16-16*α)^1 + 10334765056 * (16*α-9)^7 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c2 : (0:ℝ) ≤ 12*α^6/5 + 16*α^5/5 + 316*α^4/15 + 21*α^3/5 - 2*α^2 - α/15 - 1 := by
    have h : (0:ℝ) ≤ 90752313 * (16*α-9)^0 * (16-16*α)^6 + 1069704992 * (16*α-9)^1 * (16-16*α)^5 + 4642104832 * (16*α-9)^2 * (16-16*α)^4 + 10056621056 * (16*α-9)^3 * (16-16*α)^3 + 11748556800 * (16*α-9)^4 * (16-16*α)^2 + 7103053824 * (16*α-9)^5 * (16-16*α)^1 + 1749024768 * (16*α-9)^6 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 6)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 5))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 6)) (pow_nonneg hq 0)))
    have e : (7401835069440:ℝ) * ((12*α^6/5 + 16*α^5/5 + 316*α^4/15 + 21*α^3/5 - 2*α^2 - α/15) - 1) = 90752313 * (16*α-9)^0 * (16-16*α)^6 + 1069704992 * (16*α-9)^1 * (16-16*α)^5 + 4642104832 * (16*α-9)^2 * (16-16*α)^4 + 10056621056 * (16*α-9)^3 * (16-16*α)^3 + 11748556800 * (16*α-9)^4 * (16-16*α)^2 + 7103053824 * (16*α-9)^5 * (16-16*α)^1 + 1749024768 * (16*α-9)^6 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c3 : (0:ℝ) ≤ 11*α^5/5 + 61*α^4/5 + 91*α^3/5 - α^2 - 6*α/5 - 1 := by
    have h : (0:ℝ) ≤ 13595155 * (16*α-9)^0 * (16-16*α)^5 + 124717376 * (16*α-9)^1 * (16-16*α)^4 + 419906816 * (16*α-9)^2 * (16-16*α)^3 + 670466048 * (16*α-9)^3 * (16-16*α)^2 + 515637248 * (16*α-9)^4 * (16-16*α)^1 + 154140672 * (16*α-9)^5 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 5)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 0)))
    have e : (88117084160:ℝ) * ((11*α^5/5 + 61*α^4/5 + 91*α^3/5 - α^2 - 6*α/5) - 1) = 13595155 * (16*α-9)^0 * (16-16*α)^5 + 124717376 * (16*α-9)^1 * (16-16*α)^4 + 419906816 * (16*α-9)^2 * (16-16*α)^3 + 670466048 * (16*α-9)^3 * (16-16*α)^2 + 515637248 * (16*α-9)^4 * (16-16*α)^1 + 154140672 * (16*α-9)^5 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c4 : (0:ℝ) ≤ 16*α^4/15 + 364*α^3/15 + 152*α^2/15 - 56*α/15 - 4/15 - 1 := by
    have h : (0:ℝ) ≤ 262061 * (16*α-9)^0 * (16-16*α)^4 + 1893900 * (16*α-9)^1 * (16-16*α)^3 + 4733888 * (16*α-9)^2 * (16-16*α)^2 + 4971520 * (16*α-9)^3 * (16-16*α)^1 + 1871872 * (16*α-9)^4 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 4)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 0)))
    have e : (147517440:ℝ) * ((16*α^4/15 + 364*α^3/15 + 152*α^2/15 - 56*α/15 - 4/15) - 1) = 262061 * (16*α-9)^0 * (16-16*α)^4 + 1893900 * (16*α-9)^1 * (16-16*α)^3 + 4733888 * (16*α-9)^2 * (16-16*α)^2 + 4971520 * (16*α-9)^3 * (16-16*α)^1 + 1871872 * (16*α-9)^4 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c5 : (0:ℝ) ≤ 112*α^2/3 - 8*α/3 - 8/3 - 1 := by
    have h : (0:ℝ) ≤ 319 * (16*α-9)^0 * (16-16*α)^2 + 1464 * (16*α-9)^1 * (16-16*α)^1 + 1488 * (16*α-9)^2 * (16-16*α)^0 := (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 2)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 0)))
    have e : (2352:ℝ) * ((112*α^2/3 - 8*α/3 - 8/3) - 1) = 319 * (16*α-9)^0 * (16-16*α)^2 + 1464 * (16*α-9)^1 * (16-16*α)^1 + 1488 * (16*α-9)^2 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c6 : (0:ℝ) ≤ 48*α - 16 - 1 := by
    have h : (0:ℝ) ≤ 10 * (16*α-9)^0 * (16-16*α)^1 + 31 * (16*α-9)^1 * (16-16*α)^0 := (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 1)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 0)))
    have e : (7:ℝ) * ((48*α - 16) - 1) = 10 * (16*α-9)^0 * (16-16*α)^1 + 31 * (16*α-9)^1 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have h : (0:ℝ) ≤ 1 * θ^0 * (1-θ)^6 * ((-4*α^8 - α^7 + 18*α^6 + 11*α^5) - 1) + 6 * θ^1 * (1-θ)^5 * ((2*α^7/3 - 4*α^6/3 + 59*α^5/3 + 10*α^4 - 7*α^3/3) - 1) + 15 * θ^2 * (1-θ)^4 * ((12*α^6/5 + 16*α^5/5 + 316*α^4/15 + 21*α^3/5 - 2*α^2 - α/15) - 1) + 20 * θ^3 * (1-θ)^3 * ((11*α^5/5 + 61*α^4/5 + 91*α^3/5 - α^2 - 6*α/5) - 1) + 15 * θ^4 * (1-θ)^2 * ((16*α^4/15 + 364*α^3/15 + 152*α^2/15 - 56*α/15 - 4/15) - 1) + 6 * θ^5 * (1-θ)^1 * ((112*α^2/3 - 8*α/3 - 8/3) - 1) + 1 * θ^6 * (1-θ)^0 * ((48*α - 16) - 1) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 0)) (pow_nonneg hb 6)) c0) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 1)) (pow_nonneg hb 5)) c1)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 2)) (pow_nonneg hb 4)) c2)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 3)) (pow_nonneg hb 3)) c3)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 4)) (pow_nonneg hb 2)) c4)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 5)) (pow_nonneg hb 1)) c5)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 6)) (pow_nonneg hb 0)) c6))
  have e : (-4*α^8*θ^6 + 24*α^8*θ^5 - 60*α^8*θ^4 + 80*α^8*θ^3 - 60*α^8*θ^2 + 24*α^8*θ - 4*α^8 - 5*α^7*θ^6 + 26*α^7*θ^5 - 55*α^7*θ^4 + 60*α^7*θ^3 - 35*α^7*θ^2 + 10*α^7*θ - α^7 + 62*α^6*θ^6 - 292*α^6*θ^5 + 566*α^6*θ^4 - 584*α^6*θ^3 + 346*α^6*θ^2 - 116*α^6*θ + 18*α^6 - 103*α^5*θ^6 + 464*α^5*θ^5 - 859*α^5*θ^4 + 812*α^5*θ^3 - 377*α^5*θ^2 + 52*α^5*θ + 11*α^5 + 28*α^4*θ^6 - 264*α^4*θ^5 + 580*α^4*θ^4 - 420*α^4*θ^3 + 16*α^4*θ^2 + 60*α^4*θ + 77*α^3*θ^6 + 42*α^3*θ^5 - 210*α^3*θ^4 - 28*α^3*θ^3 + 133*α^3*θ^2 - 14*α^3*θ - 82*α^2*θ^6 - 20*α^2*θ^5 + 32*α^2*θ^4 + 100*α^2*θ^3 - 30*α^2*θ^2 + 31*α*θ^6 + 28*α*θ^5 + 10*α*θ^4 - 20*α*θ^3 - α*θ^2 - 4*θ^6 - 8*θ^5 - 4*θ^4) - 1 = 1 * θ^0 * (1-θ)^6 * ((-4*α^8 - α^7 + 18*α^6 + 11*α^5) - 1) + 6 * θ^1 * (1-θ)^5 * ((2*α^7/3 - 4*α^6/3 + 59*α^5/3 + 10*α^4 - 7*α^3/3) - 1) + 15 * θ^2 * (1-θ)^4 * ((12*α^6/5 + 16*α^5/5 + 316*α^4/15 + 21*α^3/5 - 2*α^2 - α/15) - 1) + 20 * θ^3 * (1-θ)^3 * ((11*α^5/5 + 61*α^4/5 + 91*α^3/5 - α^2 - 6*α/5) - 1) + 15 * θ^4 * (1-θ)^2 * ((16*α^4/15 + 364*α^3/15 + 152*α^2/15 - 56*α/15 - 4/15) - 1) + 6 * θ^5 * (1-θ)^1 * ((112*α^2/3 - 8*α/3 - 8/3) - 1) + 1 * θ^6 * (1-θ)^0 * ((48*α - 16) - 1) := by ring
  rw [← e] at h
  linarith

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
lemma P1r_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < P1rp α θ := by
  unfold P1rp
  have hp : (0:ℝ) ≤ 16*α-9 := by linarith
  have hq : (0:ℝ) ≤ 16-16*α := by linarith
  have ha : (0:ℝ) ≤ θ := h3.le
  have hb : (0:ℝ) ≤ 1-θ := by linarith
  have c0 : (0:ℝ) ≤ -α^6 + 3*α^4 - 1/4 := by
    have h : (0:ℝ) ≤ 313103 * (16*α-9)^0 * (16-16*α)^6 + 15074976 * (16*α-9)^1 * (16-16*α)^5 + 84145152 * (16*α-9)^2 * (16-16*α)^4 + 196575232 * (16*α-9)^3 * (16-16*α)^3 + 229834752 * (16*α-9)^4 * (16-16*α)^2 + 132120576 * (16*α-9)^5 * (16-16*α)^1 + 29360128 * (16*α-9)^6 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 6)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 5))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 6)) (pow_nonneg hq 0)))
    have e : (1973822685184:ℝ) * ((-α^6 + 3*α^4) - 1/4) = 313103 * (16*α-9)^0 * (16-16*α)^6 + 15074976 * (16*α-9)^1 * (16-16*α)^5 + 84145152 * (16*α-9)^2 * (16-16*α)^4 + 196575232 * (16*α-9)^3 * (16-16*α)^3 + 229834752 * (16*α-9)^4 * (16-16*α)^2 + 132120576 * (16*α-9)^5 * (16-16*α)^1 + 29360128 * (16*α-9)^6 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c1 : (0:ℝ) ≤ 2*α^5/5 - α^4 + 4*α^3 - 3*α^2/5 - 1/4 := by
    have h : (0:ℝ) ≤ 509825 * (16*α-9)^0 * (16-16*α)^5 + 5542696 * (16*α-9)^1 * (16-16*α)^4 + 19563008 * (16*α-9)^2 * (16-16*α)^3 + 31193088 * (16*α-9)^3 * (16-16*α)^2 + 23330816 * (16*α-9)^4 * (16-16*α)^1 + 6684672 * (16*α-9)^5 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 5)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 4))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 5)) (pow_nonneg hq 0)))
    have e : (44058542080:ℝ) * ((2*α^5/5 - α^4 + 4*α^3 - 3*α^2/5) - 1/4) = 509825 * (16*α-9)^0 * (16-16*α)^5 + 5542696 * (16*α-9)^1 * (16-16*α)^4 + 19563008 * (16*α-9)^2 * (16-16*α)^3 + 31193088 * (16*α-9)^3 * (16-16*α)^2 + 23330816 * (16*α-9)^4 * (16-16*α)^1 + 6684672 * (16*α-9)^5 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c2 : (0:ℝ) ≤ 3*α^4/5 + α^3 + 13*α^2/5 - 2*α/5 - 1/4 := by
    have h : (0:ℝ) ≤ 191923 * (16*α-9)^0 * (16-16*α)^4 + 1326992 * (16*α-9)^1 * (16-16*α)^3 + 3169792 * (16*α-9)^2 * (16-16*α)^2 + 3190784 * (16*α-9)^3 * (16-16*α)^1 + 1163264 * (16*α-9)^4 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 4)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 3))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 4)) (pow_nonneg hq 0)))
    have e : (786759680:ℝ) * ((3*α^4/5 + α^3 + 13*α^2/5 - 2*α/5) - 1/4) = 191923 * (16*α-9)^0 * (16-16*α)^4 + 1326992 * (16*α-9)^1 * (16-16*α)^3 + 3169792 * (16*α-9)^2 * (16-16*α)^2 + 3190784 * (16*α-9)^3 * (16-16*α)^1 + 1163264 * (16*α-9)^4 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c3 : (0:ℝ) ≤ 2*α^3/5 + 18*α^2/5 + 6*α/5 - 1/5 - 1/4 := by
    have h : (0:ℝ) ≤ 14697 * (16*α-9)^0 * (16-16*α)^3 + 69312 * (16*α-9)^1 * (16-16*α)^2 + 102912 * (16*α-9)^2 * (16-16*α)^1 + 48640 * (16*α-9)^3 * (16-16*α)^0 := (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 3)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 2))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 2)) (pow_nonneg hq 1))) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 3)) (pow_nonneg hq 0)))
    have e : (3512320:ℝ) * ((2*α^3/5 + 18*α^2/5 + 6*α/5 - 1/5) - 1/4) = 14697 * (16*α-9)^0 * (16-16*α)^3 + 69312 * (16*α-9)^1 * (16-16*α)^2 + 102912 * (16*α-9)^2 * (16-16*α)^1 + 48640 * (16*α-9)^3 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c4 : (0:ℝ) ≤ 32*α/5 - 1/4 := by
    have h : (0:ℝ) ≤ 67 * (16*α-9)^0 * (16-16*α)^1 + 123 * (16*α-9)^1 * (16-16*α)^0 := (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 1)) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 1)) (pow_nonneg hq 0)))
    have e : (140:ℝ) * ((32*α/5) - 1/4) = 67 * (16*α-9)^0 * (16-16*α)^1 + 123 * (16*α-9)^1 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have c5 : (0:ℝ) ≤ 8 - 1/4 := by
    have h : (0:ℝ) ≤ 31 * (16*α-9)^0 * (16-16*α)^0 := (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp 0)) (pow_nonneg hq 0))
    have e : (4:ℝ) * ((8) - 1/4) = 31 * (16*α-9)^0 * (16-16*α)^0 := by ring
    rw [← e] at h
    exact (mul_nonneg_iff_of_pos_left (by norm_num)).mp h
  have h : (0:ℝ) ≤ 1 * θ^0 * (1-θ)^5 * ((-α^6 + 3*α^4) - 1/4) + 5 * θ^1 * (1-θ)^4 * ((2*α^5/5 - α^4 + 4*α^3 - 3*α^2/5) - 1/4) + 10 * θ^2 * (1-θ)^3 * ((3*α^4/5 + α^3 + 13*α^2/5 - 2*α/5) - 1/4) + 10 * θ^3 * (1-θ)^2 * ((2*α^3/5 + 18*α^2/5 + 6*α/5 - 1/5) - 1/4) + 5 * θ^4 * (1-θ)^1 * ((32*α/5) - 1/4) + 1 * θ^5 * (1-θ)^0 * ((8) - 1/4) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 0)) (pow_nonneg hb 5)) c0) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 1)) (pow_nonneg hb 4)) c1)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 2)) (pow_nonneg hb 3)) c2)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 3)) (pow_nonneg hb 2)) c3)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 4)) (pow_nonneg hb 1)) c4)) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha 5)) (pow_nonneg hb 0)) c5))
  have e : (α^6*θ^5 - 5*α^6*θ^4 + 10*α^6*θ^3 - 10*α^6*θ^2 + 5*α^6*θ - α^6 + 2*α^5*θ^5 - 8*α^5*θ^4 + 12*α^5*θ^3 - 8*α^5*θ^2 + 2*α^5*θ - 14*α^4*θ^5 + 53*α^4*θ^4 - 78*α^4*θ^3 + 56*α^4*θ^2 - 20*α^4*θ + 3*α^4 + 14*α^3*θ^5 - 58*α^3*θ^4 + 94*α^3*θ^3 - 70*α^3*θ^2 + 20*α^3*θ + 7*α^2*θ^5 + 18*α^2*θ^4 - 60*α^2*θ^3 + 38*α^2*θ^2 - 3*α^2*θ - 16*α*θ^5 - 4*α*θ^4 + 24*α*θ^3 - 4*α*θ^2 + 6*θ^5 + 4*θ^4 - 2*θ^3) - 1/4 = 1 * θ^0 * (1-θ)^5 * ((-α^6 + 3*α^4) - 1/4) + 5 * θ^1 * (1-θ)^4 * ((2*α^5/5 - α^4 + 4*α^3 - 3*α^2/5) - 1/4) + 10 * θ^2 * (1-θ)^3 * ((3*α^4/5 + α^3 + 13*α^2/5 - 2*α/5) - 1/4) + 10 * θ^3 * (1-θ)^2 * ((2*α^3/5 + 18*α^2/5 + 6*α/5 - 1/5) - 1/4) + 5 * θ^4 * (1-θ)^1 * ((32*α/5) - 1/4) + 1 * θ^5 * (1-θ)^0 * ((8) - 1/4) := by ring
  rw [← e] at h
  linarith

end YP3Alg

namespace YP3Alg2
open YP3Alg

noncomputable def F (α θ x : ℝ) : ℝ :=
  (α*(1-θ)+θ)^2*(α*(1-θ)-x)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) - ((α*(1-θ)+θ)-x)^2/(16*(α^2*(1-θ)+θ))
    - (α-x)^2/(16*α^2) + ((α*(1-θ)+θ)-x)^2/(16*(α*(1-θ)+θ))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
lemma F_x1 (α θ t : ℝ) (h2 : 0 < α) (h3 : 0 < θ) (h4 : θ < 1) :
    F α θ (α*(1-θ)*((α*(1-θ)+θ)^2+θ-2*θ*t)/(α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2))
      = (P0p α θ + P1p α θ*t + qp α θ*(t^2 - α*(α*(1-θ)+θ)*(1-α)*(1-θ)))
        / (16*(α*(1-θ)+θ)*(α^2*(1-θ)+θ)*(α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2)^2) := by
  have hθ1 : (1-θ) ≠ 0 := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  have hD : 0 < α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2 := by
    have : 0 < 1-θ := by linarith
    positivity
  unfold F P0p P1p qp
  set μ := α*(1-θ)+θ with hμd
  set s := α^2*(1-θ)+θ with hsd
  set D := α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2 with hDd
  have hD' := hD.ne'
  have hμ' := hμ.ne'
  have hs' := hs.ne'
  have hα' := h2.ne'
  field_simp
  rw [hμd, hsd, hDd]
  ring


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
lemma F1_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < F α θ (α*(1-θ)*((α*(1-θ)+θ)^2+θ-2*θ*Real.sqrt (α*(α*(1-θ)+θ)*(1-α)*(1-θ)))/(α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2)) := by
  have ha0 : 0 < α := by linarith
  rw [F_x1 α θ _ ha0 h3 h4]
  have hθ' : 0 < 1 - θ := by linarith
  have hα' : 0 < 1 - α := by linarith
  have hμ1 : α*(1-θ)+θ < 1 := by nlinarith
  have hμ0 : 0 < α*(1-θ)+θ := by nlinarith
  have hz0 : 0 < α*(α*(1-θ)+θ)*(1-α)*(1-θ) := by positivity
  have hz1 : α*(α*(1-θ)+θ)*(1-α)*(1-θ) < 1 := by
    have e1 : α*(α*(1-θ)+θ) < 1 := by nlinarith
    have e2 : (1-α)*(1-θ) < 1 := by nlinarith
    have e3 : 0 < (1-α)*(1-θ) := by positivity
    calc α*(α*(1-θ)+θ)*(1-α)*(1-θ) = (α*(α*(1-θ)+θ))*((1-α)*(1-θ)) := by ring
      _ < 1 * 1 := by
        apply mul_lt_mul'' e1 e2 (by positivity) e3.le
      _ = 1 := by ring
  set z := α*(α*(1-θ)+θ)*(1-α)*(1-θ) with hzd
  have ht : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0.le
  have htz : z < Real.sqrt z := by
    rw [Real.lt_sqrt hz0.le]; nlinarith
  set t := Real.sqrt z
  have hR := R_pos α θ h1 h2 h3 h4
  have hP := P1r_pos α θ h1 h2 h3 h4
  have eA : P1p α θ = 4*θ^2*P1rp α θ := by unfold P1p P1rp; ring
  have eB : P0p α θ + P1p α θ * z = θ^2*(1-α)*(1-θ)*Rp α θ := by rw [hzd]; unfold P0p P1p Rp; ring
  have e1 : P0p α θ + P1p α θ*t + qp α θ*(t^2 - z)
      = θ^2*(1-α)*(1-θ)*Rp α θ + 4*θ^2*P1rp α θ*(t - z) + qp α θ*(t^2-z) := by
    rw [← eB, ← eA]; ring
  rw [e1, ht, sub_self, mul_zero, add_zero]
  apply div_pos
  · apply add_pos
    · apply mul_pos _ hR; positivity
    · apply mul_pos _ (by linarith); apply mul_pos _ hP; positivity
  · have : 0 < α^2*(1-θ)+θ := by positivity
    have : 0 < α^2*(1-θ)^3+4*α*θ*(1-θ)+θ*(1+θ)^2 := by positivity
    positivity

end YP3Alg2

open YieldPostpone.Interplay YP3Alg2

lemma yp3_mid (a b α θ c : ℝ) (ha : 0 < a) (hb : 0 < b) (h2 : 0 < α) (h3 : 0 < θ) (h4 : θ < 1) :
    (α*(1-θ)+θ)^2*(a*α*(1-θ)-b*c)^2/(4*b*α^2*(1-θ)^2*(α^2*(1-θ)+θ))
      - (a*(α*(1-θ)+θ)-b*c)^2/(16*b*(α^2*(1-θ)+θ))
      - ((b*c-a*α)^2/(16*b*α^2) - (a*(α*(1-θ)+θ)-b*c)^2/(16*b*(α*(1-θ)+θ)))
      = a^2/b * F α θ (b*c/a) := by
  have hθ1 : (1-θ) ≠ 0 := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  have := hμ.ne'; have := hs.ne'; have := h2.ne'; have := ha.ne'; have := hb.ne'
  unfold F
  field_simp
  ring

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    0 < μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * cDR1 P) ^ 2 /
          (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))
        - (P.a * μ P - P.b * cDR1 P) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))
        - ((P.b * cDR1 P - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2)
          - (P.a * μ P - P.b * cDR1 P) ^ 2 / (16 * P.b * μ P)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hD : 0 < P.α^2*(1-P.θ)^3+4*P.α*P.θ*(1-P.θ)+P.θ*(1+P.θ)^2 := by
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hc1 : P.b * cDR1 P / P.a = P.α*(1-P.θ)*((P.α*(1-P.θ)+P.θ)^2+P.θ-2*P.θ*Real.sqrt (P.α*(P.α*(1-P.θ)+P.θ)*(1-P.α)*(1-P.θ)))/(P.α^2*(1-P.θ)^3+4*P.α*P.θ*(1-P.θ)+P.θ*(1+P.θ)^2) := by
    unfold cDR1 μ; field_simp
  have e := yp3_mid P.a P.b P.α P.θ (cDR1 P) ha hb hα0 hθ0 hθ1
  have hF := F1_pos P.α P.θ hα hα1 hθ0 hθ1
  rw [← hc1] at hF
  have : μ P = P.α * (1 - P.θ) + P.θ := rfl
  rw [this, e]
  positivity
