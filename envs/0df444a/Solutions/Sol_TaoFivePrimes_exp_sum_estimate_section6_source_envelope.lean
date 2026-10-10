-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_section6_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T09:08:04.284545+00:00
-- url     : https://prove2.me/submissions/9b080c0d-5618-4c4f-a9d0-75d749d04274

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_vaughan_modulus_two_source
import Theorems.Thm_TaoFivePrimes_small_q_modulus_transfer_source_envelope
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_envelope

set_option autoImplicit false
set_option maxRecDepth 10000


-- Source module: Theorems.Thm_TaoFivePrimes_exp_sum_estimate_section6_modulus_two_source
section
set_option maxHeartbeats 2000000

namespace TaoFivePrimes

private lemma fifth_root_ge_ten_thousand
    (x : ℝ) (hx : (10 : ℝ) ^ 20 ≤ x) :
    (10000 : ℝ) ≤ x ^ (1 / 5 : ℝ) := by
  have hbase : ((10000 : ℝ) ^ (5 : ℕ)) ≤ x := by
    norm_num at hx ⊢
    exact hx
  have hr := Real.rpow_le_rpow
    (show (0 : ℝ) ≤ (10000 : ℝ) ^ (5 : ℕ) by positivity)
    hbase (show (0 : ℝ) ≤ 1 / 5 by norm_num)
  have hroot : (((10000 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ)) = 10000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [hroot] at hr

theorem exp_sum_estimate_section6_modulus_two_source
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
      (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) := by
  let t : ℝ := x ^ (1 / 5 : ℝ)
  let U : ℝ := t ^ 2 / 4
  let V : ℝ := t ^ 2 / 2
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hx0 : 0 ≤ x := hxpos.le
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have htpos : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos hxpos _
  have ht0 : 0 ≤ t := htpos.le
  have htne : t ≠ 0 := ne_of_gt htpos
  have htlarge : (10000 : ℝ) ≤ t := by
    dsimp [t]
    exact fifth_root_ge_ten_thousand x hx
  have htone : (1 : ℝ) ≤ t := by linarith only [htlarge]
  have ht2 : t ^ 2 = x ^ (2 / 5 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have ht3 : t ^ 3 = x ^ (3 / 5 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have ht4 : t ^ 4 = x ^ (4 / 5 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have ht5 : t ^ 5 = x := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have ht4nonneg : 0 ≤ t ^ 4 := by positivity
  have ht4pos : 0 < t ^ 4 := by positivity
  have ht4lower : (10000 : ℝ) ^ 4 ≤ t ^ 4 :=
    pow_le_pow_left₀ (by norm_num) htlarge 4
  have ht4le5 : t ^ 4 ≤ t ^ 5 := by
    calc
      t ^ 4 = t ^ 4 * 1 := by ring
      _ ≤ t ^ 4 * t := mul_le_mul_of_nonneg_left htone ht4nonneg
      _ = t ^ 5 := by ring
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hU40 : (40 : ℝ) ≤ U := by
    dsimp [U]
    nlinarith only [htlarge, sq_nonneg t]
  have hV40 : (40 : ℝ) ≤ V := by
    dsimp [V]
    nlinarith only [htlarge, sq_nonneg t]
  have hUone : (1 : ℝ) ≤ U := le_trans (by norm_num) hU40
  have hVone : (1 : ℝ) ≤ V := le_trans (by norm_num) hV40
  have hUVeq : U * V = t ^ 4 / 8 := by
    dsimp [U, V]
    ring
  have hUV : U * V ≤ x / 4 := by
    rw [hUVeq, ← ht5]
    linarith only [ht4le5, ht4nonneg]
  have hUleUV : U ≤ U * V := by
    calc
      U = U * 1 := by ring
      _ ≤ U * V := mul_le_mul_of_nonneg_left hVone hU0
  have hVleUV : V ≤ U * V := by
    calc
      V = 1 * V := by ring
      _ ≤ U * V := mul_le_mul_of_nonneg_right hUone hV0
  have hxdiv4lt : x / 4 < x := by linarith only [hxpos]
  have hUx : U < x := hUleUV.trans_lt (hUV.trans_lt hxdiv4lt)
  have hVx : V < x := hVleUV.trans_lt (hUV.trans_lt hxdiv4lt)
  have hUV2eq : U * V ^ 2 = x * t / 16 := by
    dsimp [U, V]
    rw [← ht5]
    ring
  have hUV2 : x ≤ U * V ^ 2 := by
    rw [hUV2eq]
    have hm : 0 ≤ x * (t - 16) := mul_nonneg hx0 (by linarith only [htlarge])
    nlinarith only [hm]
  have hqposN : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposN
  have hq0 : (0 : ℝ) ≤ q := hqpos.le
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hq100 : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have hqx' : (q : ℝ) ≤ x := by
    calc
      (q : ℝ) ≤ x / 100 := hqx
      _ ≤ x := by linarith only [hx0]
  have hq4 : 4 ≤ q := le_trans (by norm_num) hq
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqposN)
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log x :=
    Real.log_le_log hqpos hqx'
  have hlog2 : Real.log 2 ≤ (0.9 : ℝ) :=
    le_trans Real.log_two_lt_d9.le (by norm_num)
  have hlog4 : Real.log 4 ≤ (1.8 : ℝ) := by
    rw [Real.log_four_eq]
    linarith only [hlog2]
  have hlog10 : (2.3 : ℝ) ≤ Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlogmono : Real.log ((10 : ℝ) ^ 20) ≤ Real.log x :=
    Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hlogmono
  norm_num at hlogmono
  have hlogx46 : (46 : ℝ) ≤ Real.log x := by linarith only [hlogmono, hlog10]
  have hP0 : 0 ≤ Real.log x * (Real.log x + 11.3) := by positivity
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) hxne]
  have hlog2x0 : 0 ≤ Real.log (2 * x) :=
    Real.log_nonneg (by linarith only [hx])

  have harg1 : 2 * U * V / q + 4 = t ^ 4 / (4 * q) + 4 := by
    calc
      2 * U * V / q + 4 = 2 * (U * V) / q + 4 := by ring
      _ = t ^ 4 / (4 * q) + 4 := by rw [hUVeq]; ring
  have hxUV : x / (U * V) = 8 * t := by
    rw [hUVeq, ← ht5]
    field_simp [htne]
  have hVxU : V * x / U = 2 * x := by
    dsimp [U, V]
    field_simp [htne]
    ring
  have hxU : x / U = 4 * t ^ 3 := by
    dsimp [U]
    rw [← ht5]
    field_simp [htne]
  have hxratio : x / (x / (q : ℝ)) = q := by field_simp

  have harg1_le : t ^ 4 / (4 * (q : ℝ)) + 4 ≤ t ^ 4 := by
    have hden : (400 : ℝ) ≤ 4 * q := by linarith only [hq100]
    have hdiv : t ^ 4 / (4 * (q : ℝ)) ≤ t ^ 4 / 400 :=
      div_le_div_of_nonneg_left ht4nonneg (by norm_num) hden
    have hfour : t ^ 4 / 400 + 4 ≤ t ^ 4 := by
      nlinarith only [ht4lower]
    linarith only [hdiv, hfour]
  have harg1pos : 0 < t ^ 4 / (4 * (q : ℝ)) + 4 := by positivity
  have hlogarg1 : Real.log (t ^ 4 / (4 * (q : ℝ)) + 4) ≤
      (0.8 : ℝ) * Real.log x := by
    calc
      Real.log (t ^ 4 / (4 * (q : ℝ)) + 4) ≤ Real.log (t ^ 4) :=
        Real.log_le_log harg1pos harg1_le
      _ = Real.log (x ^ (4 / 5 : ℝ)) := by rw [ht4]
      _ = (0.8 : ℝ) * Real.log x := by
        rw [Real.log_rpow hxpos]
        norm_num
  have hterm1 :
      0.5 * (x / q) * Real.log x *
          Real.log (t ^ 4 / (4 * q) + 4) ≤
        0.4 * (x / q) * (Real.log x * (Real.log x + 11.3)) := by
    have hc : 0 ≤ 0.5 * (x / (q : ℝ)) * Real.log x := by positivity
    calc
      _ = (0.5 * (x / q) * Real.log x) *
          Real.log (t ^ 4 / (4 * q) + 4) := by ring
      _ ≤ (0.5 * (x / q) * Real.log x) *
          (0.8 * Real.log x) :=
        mul_le_mul_of_nonneg_left hlogarg1 hc
      _ = 0.4 * (x / q) * (Real.log x * Real.log x) := by ring
      _ ≤ 0.4 * (x / q) * (Real.log x * (Real.log x + 11.3)) := by
        gcongr
        linarith only []

  have hfactorI : (8 + Real.log (q : ℝ)) * Real.log (2 * x) ≤
      1.1 * Real.log x * (Real.log x + 11.3) := by
    have hfirst : 8 + Real.log (q : ℝ) ≤ 8 + Real.log x := by linarith only [hlogq_le]
    have hsecond : Real.log (2 * x) ≤ Real.log x + 0.9 := by
      rw [hlog2x]
      linarith only [hlog2]
    have hleft0 : 0 ≤ 8 + Real.log (q : ℝ) := by linarith only [hlogq0]
    have hright0 : 0 ≤ Real.log x + 0.9 := by linarith only [hlogx0]
    calc
      (8 + Real.log (q : ℝ)) * Real.log (2 * x) ≤
          (8 + Real.log x) * (Real.log x + 0.9) :=
        mul_le_mul hfirst hsecond hlog2x0 (by linarith only [hlogx0])
      _ ≤ 1.1 * Real.log x * (Real.log x + 11.3) := by
        nlinarith only [hlogx46, sq_nonneg (Real.log x)]
  have htermI :
      0.89 * (t ^ 4 / 8 + (5 / 2 : ℝ) * q) *
          (8 + Real.log q) * Real.log (2 * x) ≤
        (0.122375 * t ^ 4 + 2.4475 * q) *
          (Real.log x * (Real.log x + 11.3)) := by
    have hc : 0 ≤ 0.89 * (t ^ 4 / 8 + (5 / 2 : ℝ) * q) := by positivity
    calc
      _ = (0.89 * (t ^ 4 / 8 + (5 / 2 : ℝ) * q)) *
          ((8 + Real.log q) * Real.log (2 * x)) := by ring
      _ ≤ (0.89 * (t ^ 4 / 8 + (5 / 2 : ℝ) * q)) *
          (1.1 * Real.log x * (Real.log x + 11.3)) :=
        mul_le_mul_of_nonneg_left hfactorI hc
      _ = (0.122375 * t ^ 4 + 2.4475 * q) *
          (Real.log x * (Real.log x + 11.3)) := by ring

  have h8t_le_x : 8 * t ≤ x := by
    have h8 : (8 : ℝ) ≤ t ^ 4 := by linarith only [ht4lower]
    calc
      8 * t ≤ t ^ 4 * t := mul_le_mul_of_nonneg_right h8 ht0
      _ = x := by rw [← ht5]; ring
  have hlog8t0 : 0 ≤ Real.log (8 * t) :=
    Real.log_nonneg (by linarith only [htlarge])
  have hlog8t : Real.log (8 * t) ≤ Real.log x :=
    Real.log_le_log (by positivity) h8t_le_x
  have hlogprodII : Real.log (8 * t) * Real.log (2 * x) ≤
      Real.log x * (Real.log x + 11.3) := by
    have hsecond : Real.log (2 * x) ≤ Real.log x + 11.3 := by
      rw [hlog2x]
      linarith only [hlog2]
    exact mul_le_mul hlog8t hsecond hlog2x0 hlogx0
  have hcoefII0 : 0 ≤
      0.1 * (x / Real.sqrt q) +
        0.39 * (x / Real.sqrt (x / q)) := by positivity
  have htermII :
      (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
          Real.log (8 * t) * Real.log (2 * x) ≤
        (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
          (Real.log x * (Real.log x + 11.3)) := by
    calc
      _ = (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
            (Real.log (8 * t) * Real.log (2 * x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogprodII hcoefII0

  have hsqrtU : Real.sqrt U = t / 2 := by
    calc
      Real.sqrt U = Real.sqrt ((t / 2) ^ 2) := by
        congr 1
        dsimp [U]
        ring
      _ = |t / 2| := Real.sqrt_sq_eq_abs _
      _ = t / 2 := abs_of_nonneg (by positivity)
  have hsqrtVlower : 2 * t / 3 ≤ Real.sqrt V := by
    apply Real.le_sqrt_of_sq_le
    dsimp [V]
    nlinarith only [sq_nonneg t]
  have hfracU : x / Real.sqrt U = 2 * t ^ 4 := by
    rw [hsqrtU, ← ht5]
    field_simp [htne]
  have hfracV : x / Real.sqrt V ≤ 1.5 * t ^ 4 := by
    have hdenpos : 0 < 2 * t / 3 := by positivity
    calc
      x / Real.sqrt V ≤ x / (2 * t / 3) :=
        div_le_div_of_nonneg_left hx0 hdenpos hsqrtVlower
      _ = 1.5 * t ^ 4 := by
        rw [← ht5]
        field_simp [htne]
        ring
  have hcoefIV :
      0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V) ≤
        2.27 * t ^ 4 := by
    rw [hfracU]
    nlinarith only [hfracV]
  have hlogxU : Real.log (4 * t ^ 3) =
      Real.log 4 + (0.6 : ℝ) * Real.log x := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 htne), Real.log_pow]
    dsimp [t]
    rw [Real.log_rpow hxpos]
    ring
  have ht3one : (1 : ℝ) ≤ t ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) htone 3
  have hlogxU0 : 0 ≤ Real.log (4 * t ^ 3) :=
    Real.log_nonneg (by linarith only [ht3one])
  have hlogxUbound : Real.log (4 * t ^ 3) ≤
      1.8 + 0.6 * Real.log x := by
    rw [hlogxU]
    linarith only [hlog4]
  have hnumericIV :
      2.27 * (1.8 + 0.6 * Real.log x) ≤
        0.026625 * Real.log x * (Real.log x + 11.3) := by
    nlinarith only [hlogx46, sq_nonneg (Real.log x - 46)]
  have htermIV :
      (0.55 * (x / Real.sqrt U) +
          0.78 * (x / Real.sqrt V)) * Real.log (4 * t ^ 3) ≤
        0.026625 * t ^ 4 *
          (Real.log x * (Real.log x + 11.3)) := by
    have hcoef0 : 0 ≤
        0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V) := by
      positivity
    have hbound0 : 0 ≤ 1.8 + 0.6 * Real.log x := by linarith only [hlogx0]
    calc
      _ ≤ (0.55 * (x / Real.sqrt U) +
          0.78 * (x / Real.sqrt V)) *
            (1.8 + 0.6 * Real.log x) :=
        mul_le_mul_of_nonneg_left hlogxUbound hcoef0
      _ ≤ (2.27 * t ^ 4) * (1.8 + 0.6 * Real.log x) :=
        mul_le_mul_of_nonneg_right hcoefIV hbound0
      _ = t ^ 4 * (2.27 * (1.8 + 0.6 * Real.log x)) := by ring
      _ ≤ t ^ 4 *
          (0.026625 * Real.log x * (Real.log x + 11.3)) :=
        mul_le_mul_of_nonneg_left hnumericIV ht4nonneg
      _ = _ := by ring

  have hsource := exp_sum_estimate_vaughan_modulus_two_source
    x alpha beta U V a q hq4 haq halpha hbeta hU40 hV40 hUx hVx
      hUV hUV2
  rw [harg1, hxUV, hVxU, hxU, hUVeq] at hsource
  have hbracket :
      0.4 * (x / (q : ℝ)) +
          (0.122375 * t ^ 4 + 2.4475 * q) +
          (0.1 * (x / Real.sqrt q) +
            0.39 * (x / Real.sqrt (x / q))) +
          0.026625 * t ^ 4 ≤
        0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ) := by
    rw [hxratio, ← ht4]
    linarith only [hq0]
  calc
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
        0.5 * (x / q) * Real.log x *
            Real.log (t ^ 4 / (4 * q) + 4) +
          0.89 * (t ^ 4 / 8 + (5 / 2 : ℝ) * q) *
            (8 + Real.log q) * Real.log (2 * x) +
          (0.1 * (x / Real.sqrt q) +
            0.39 * (x / Real.sqrt (x / q))) *
              Real.log (8 * t) * Real.log (2 * x) +
          (0.55 * (x / Real.sqrt U) +
            0.78 * (x / Real.sqrt V)) * Real.log (4 * t ^ 3) := hsource
    _ ≤ 0.4 * (x / q) * (Real.log x * (Real.log x + 11.3)) +
        (0.122375 * t ^ 4 + 2.4475 * q) *
          (Real.log x * (Real.log x + 11.3)) +
        (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
            (Real.log x * (Real.log x + 11.3)) +
        0.026625 * t ^ 4 *
          (Real.log x * (Real.log x + 11.3)) := by
      exact add_le_add (add_le_add (add_le_add hterm1 htermI) htermII) htermIV
    _ = (0.4 * (x / q) +
          (0.122375 * t ^ 4 + 2.4475 * q) +
          (0.1 * (x / Real.sqrt q) +
            0.39 * (x / Real.sqrt (x / q))) +
          0.026625 * t ^ 4) *
        (Real.log x * (Real.log x + 11.3)) := by ring
    _ ≤ (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        (Real.log x * (Real.log x + 11.3)) :=
      mul_le_mul_of_nonneg_right hbracket hP0
    _ = (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) := by ring

end TaoFivePrimes
end


-- Source module: Theorems.Thm_TaoFivePrimes_eta0_modulus_to_two_2016
section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem eta0_modulus_to_two_le_2016_sqrt
    (x alpha : ℝ) (q : ℕ) (hx : (10 : ℝ) ^ 20 ≤ x) (hqne : q ≠ 0)
    (hq : ∀ p ∈ q.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q x alpha - smoothedExpSum eta0 2 x alpha‖ ≤
      20.16 * Real.sqrt x := by
  exact small_q_modulus_transfer_source_envelope x alpha q hx
    (Nat.pos_of_ne_zero hqne) hq

theorem smoothedExpSum_eta0_zero_modulus (x alpha : ℝ) :
    smoothedExpSum eta0 0 x alpha = 0 := by
  unfold smoothedExpSum
  calc
    (∑' n : ℕ,
        if n.Coprime 0 then
          (Λ n : ℂ) * expCircle (alpha * n) * (eta0 ((n : ℝ) / x) : ℂ)
        else 0) = ∑' _n : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 1 <;> simp [Nat.coprime_zero_right, hn]
    _ = 0 := tsum_zero

end TaoFivePrimes
end


-- Source module: Solutions.Sol_TaoFivePrimes_exp_sum_estimate_section6_source_envelope_standalone
section
namespace TaoFivePrimes

private theorem section6_envelope_modulus_reduction
    (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) +
      20.16 * Real.sqrt x := by
  let M : ℝ :=
    (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
        2.45 * (x / (x / q)) +
        0.39 * (x / Real.sqrt (x / q)) +
        0.149 * x ^ (4 / 5 : ℝ)) *
      Real.log x * (Real.log x + 11.3)
  have hbase : ‖smoothedExpSum eta0 2 x alpha‖ ≤ M := by
    dsimp [M]
    exact exp_sum_estimate_section6_modulus_two_source
      x alpha beta a q hx hq hqx haq halpha hbeta
  by_cases hqzero : q0 = 0
  · subst q0
    rw [smoothedExpSum_eta0_zero_modulus, norm_zero]
    have hM : 0 ≤ M := (norm_nonneg _).trans hbase
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    dsimp [M] at hM ⊢
    nlinarith
  · have htransfer := eta0_modulus_to_two_le_2016_sqrt
      x alpha q0 hx hqzero hq0
    calc
      ‖smoothedExpSum eta0 q0 x alpha‖ =
          ‖(smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha) +
            smoothedExpSum eta0 2 x alpha‖ := by
          congr 1
          ring
      _ ≤ ‖smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha‖ +
          ‖smoothedExpSum eta0 2 x alpha‖ := norm_add_le _ _
      _ ≤ 20.16 * Real.sqrt x + M := add_le_add htransfer hbase
      _ = M + 20.16 * Real.sqrt x := by ring

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) +
      20.16 * Real.sqrt x := by
  exact section6_envelope_modulus_reduction
    x alpha beta a q q0 hx hq hqx haq halpha hbeta hq0
end


#print axioms solution
