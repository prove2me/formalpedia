-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_to_exp23
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T16:33:35.262797+00:00
-- url     : https://prove2.me/submissions/4cc3afa3-6359-4946-a988-d132f2df88ea

import Mathlib
import Definitions.Def_dusart_mesh_upper_seed_tight
import Definitions.Def_dusart_mesh_large_lower
import Theorems.Thm_dusart_theta_mesh_complete_upper_chain
import Theorems.Thm_TaoFivePrimes_rosser_psi_finite_middle

set_option maxHeartbeats 3000000

private lemma exp23_le_ten_billion : Real.exp 23 ≤ 10000000000 := by
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 23
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma exp20_ge_two_hundred_million : (200000000 : ℝ) ≤ Real.exp 20 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 20
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

private lemma psi_under_104 (z : ℝ) (hz : 1001 ≤ z) (hZ : z < 10^8) :
    Chebyshev.psi z ≤ (104 / 100 : ℝ) * z := by
  have hz0 : 0 ≤ z := by linarith
  have hnlo : 1000 < Nat.floor z := by
    have hn : 1001 ≤ Nat.floor z := Nat.le_floor (by linarith : (1001:ℝ) ≤ z)
    omega
  have hnhi : Nat.floor z < 10^8 := by
    have hh : (Nat.floor z : ℝ) ≤ z := Nat.floor_le hz0
    exact_mod_cast (show ((Nat.floor z : ℕ) : ℝ) < (10^8:ℝ) by linarith)
  have h := TaoFivePrimes.rosser_psi_finite_middle (Nat.floor z) hnlo hnhi
  rw [Chebyshev.psi_eq_psi_coe_floor]
  have hfloor : ((Nat.floor z : ℕ) : ℝ) ≤ z := Nat.floor_le hz0
  linarith only [h, hfloor, hz0]

private lemma pow_third_le_2200 (y : ℝ) (hy : 0 ≤ y) (hY : y ≤ 10^10) :
    y ^ ((3 : ℝ)⁻¹) ≤ 2200 := by
  have he : (y ^ ((3 : ℝ)⁻¹))^3 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity : (0:ℝ) ≤ 2200)
  rw [he]
  norm_num
  linarith

private lemma pow_fifth_le_100 (y : ℝ) (hy : 0 ≤ y) (hY : y ≤ 10^10) :
    y ^ ((5 : ℝ)⁻¹) ≤ 100 := by
  have he : (y ^ ((5 : ℝ)⁻¹))^5 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by positivity : (0:ℝ) ≤ 100)
  rw [he]
  norm_num
  linarith

theorem solution (y : ℝ) (hy : 10 ^ 8 ≤ y)
    (hupper : y < Real.exp 23) : |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hY : y ≤ (10^10:ℝ) := by
    norm_num
    exact (le_of_lt hupper).trans exp23_le_ten_billion
  have hslo : (10000 : ℝ) ≤ Real.sqrt y := by
    have := Real.sqrt_le_sqrt (show (100000000 : ℝ) ≤ y by linarith)
    norm_num at this
    exact this
  have hshi : Real.sqrt y < 10^8 := by
    have hs : Real.sqrt y ≤ 100000 := by
      have := Real.sqrt_le_sqrt hY
      norm_num at this
      exact this
    linarith
  have hs2 : (Real.sqrt y)^2 = y := Real.sq_sqrt hy0
  have hsqpsi := psi_under_104 (Real.sqrt y) (by linarith) hshi
  have hcube := pow_third_le_2200 y hy0 hY
  have hfifth := pow_fifth_le_100 y hy0 hY
  have h2200 := psi_under_104 2200 (by norm_num) (by norm_num)
  have h1001 := psi_under_104 1001 (by norm_num) (by norm_num)
  have hprimepow := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi y
  have hpow : Chebyshev.psi y - Chebyshev.theta y ≤ (14/10:ℝ)*Real.sqrt y := by
    have hsqrt : y ^ ((2 : ℝ)⁻¹) = Real.sqrt y := by rw [Real.sqrt_eq_rpow]; norm_num
    rw [hsqrt] at hprimepow
    have hc := Chebyshev.psi_mono hcube
    have hf := Chebyshev.psi_mono (hfifth.trans (by norm_num : (100:ℝ) ≤ 1001))
    linarith only [hprimepow, hsqpsi, hc, hf, h2200, h1001, hslo]
  have htheta_lower := DusartFiniteMesh.large_theta_lower y (by norm_num at hy ⊢; exact hy) (by norm_num at hY ⊢; exact hY)
  have htheta_upper := (dusart_theta_mesh_complete_upper_chain DusartMeshUpper.theta_seed_tight).2 y
      (by norm_num at hy ⊢; exact hy) (by linarith)
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog23 : Real.log y < 23 := by
    have := Real.log_lt_log hypos hupper
    simpa using this
  have hbudget_nonneg : 0 < 40 * Real.log y := by positivity
  apply abs_le.2
  constructor
  · apply (neg_le_iff_add_nonneg).2
    have h1 : (10:ℝ) * Real.sqrt y ≤ y / (40 * Real.log y) := by
      apply (le_div_iff₀ hbudget_nonneg).2
      have hm := mul_nonneg (Real.sqrt_nonneg y) (show (0:ℝ) ≤ 10000 - 400 * Real.log y by linarith)
      nlinarith only [hm, hs2, hslo]
    have htheta := Chebyshev.theta_le_psi y
    linarith only [htheta_lower, htheta, h1]
  · apply (le_div_iff₀ hbudget_nonneg).2
    have herror : Chebyshev.psi y - y ≤ 100000 + y / 10000 + (14/10:ℝ)*Real.sqrt y := by linarith only [htheta_upper, hpow]
    by_cases hsmall : y < 200000000
    · have hlog20 : Real.log y < 20 := by
        have hh := Real.log_lt_log hypos (hsmall.trans_le exp20_ge_two_hundred_million)
        simpa using hh
      have hb : 100000 + y / 10000 + (14/10:ℝ)*Real.sqrt y ≤ y / 800 := by
        have hm := mul_nonneg (Real.sqrt_nonneg y) (show (0:ℝ) ≤ Real.sqrt y - 10000 by linarith)
        nlinarith only [hm, hs2, hy] 
      have hE : Chebyshev.psi y - y ≤ y/800 := le_trans herror hb
      by_cases hpos : 0 ≤ Chebyshev.psi y - y
      · have hm := mul_nonneg hpos (show (0:ℝ) ≤ 800 - 40*Real.log y by linarith)
        nlinarith only [hE, hm]
      · nlinarith only [hpos, hbudget_nonneg, hypos]
    · have hybig : (200000000:ℝ) ≤ y := le_of_not_gt hsmall
      have hb : 100000 + y / 10000 + (14/10:ℝ)*Real.sqrt y ≤ y / 920 := by
        have hm := mul_nonneg (Real.sqrt_nonneg y) (show (0:ℝ) ≤ Real.sqrt y - 10000 by linarith)
        nlinarith only [hm, hs2, hybig] 
      have hE : Chebyshev.psi y - y ≤ y/920 := le_trans herror hb
      by_cases hpos : 0 ≤ Chebyshev.psi y - y
      · have hm := mul_nonneg hpos (show (0:ℝ) ≤ 920 - 40*Real.log y by linarith)
        nlinarith only [hE, hm]
      · nlinarith only [hpos, hbudget_nonneg, hypos]
