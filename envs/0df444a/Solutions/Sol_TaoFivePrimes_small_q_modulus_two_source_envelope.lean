-- Prove2me | solution 1 for TaoFivePrimes.small_q_modulus_two_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:45:54.424446+00:00
-- url     : https://prove2.me/submissions/016cb796-3eed-44f9-976a-865b1ab77610

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_vaughan_modulus_two_source
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_envelope

set_option autoImplicit false
set_option maxRecDepth 10000


-- Source module: Theorems.Thm_TaoFivePrimes_exp_sum_estimate_small_q_modulus_two_source
section
namespace TaoFivePrimes

private lemma cube_root_ge_four_million
    (x : ℝ) (hx : (10 : ℝ) ^ 20 ≤ x) :
    (4000000 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
  have hbase : ((4000000 : ℝ) ^ (3 : ℕ)) ≤ x := by
    norm_num at hx ⊢
    linarith
  have hr := Real.rpow_le_rpow
    (show (0 : ℝ) ≤ (4000000 : ℝ) ^ (3 : ℕ) by positivity)
    hbase (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  have hroot : (((4000000 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) = 4000000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [hroot] at hr

theorem exp_sum_estimate_small_q_modulus_two_source
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) := by
  let U : ℝ := x / (q : ℝ) ^ 2
  let V : ℝ := q
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hx0 : 0 ≤ x := hxpos.le
  have hqposN : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposN
  have hq0 : (0 : ℝ) ≤ q := hqpos.le
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqposN
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith)
  have hqcube : (q : ℝ) ^ 3 ≤ x := by
    calc
      (q : ℝ) ^ 3 ≤ (x ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hq0 hsmall 3
      _ = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
        norm_num
  have hUq : (q : ℝ) ≤ U := by
    dsimp [U]
    apply (le_div_iff₀ (sq_pos_of_pos hqpos)).2
    nlinarith
  have hU40 : (40 : ℝ) ≤ U := by
    have hq100 : (100 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hV40 : (40 : ℝ) ≤ V := by
    dsimp [V]
    exact_mod_cast (le_trans (by norm_num) hq)
  have hUx : U < x := by
    dsimp [U]
    apply (div_lt_iff₀ (sq_pos_of_pos hqpos)).2
    have hq_sq_gt : (1 : ℝ) < (q : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hVx : V < x := by
    dsimp [V]
    have hqx' : (q : ℝ) ≤ x / 100 := hqx
    have : x / 100 < x := by nlinarith
    exact hqx'.trans_lt this
  have hUVeq : U * V = x / q := by
    dsimp [U, V]
    field_simp
  have hq4 : 4 ≤ q := le_trans (by norm_num) hq
  have hUV : U * V ≤ x / 4 := by
    rw [hUVeq]
    exact div_le_div_of_nonneg_left hx0 (by norm_num) (by exact_mod_cast hq4)
  have hUV2eq : U * V ^ 2 = x := by
    dsimp [U, V]
    field_simp
  have hUV2 : x ≤ U * V ^ 2 := hUV2eq.ge
  have hroot := cube_root_ge_four_million x hx
  have hroot0 : 0 ≤ x ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx0 _
  have hqsq : (q : ℝ) ^ 2 ≤ (x ^ (1 / 3 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hq0 hsmall 2
  have hrootcube : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hfourmillion : (4000000 : ℝ) * (q : ℝ) ^ 2 ≤ x := by
    calc
      (4000000 : ℝ) * (q : ℝ) ^ 2 ≤
          x ^ (1 / 3 : ℝ) * (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
      _ ≤ x ^ (1 / 3 : ℝ) * (x ^ (1 / 3 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hqsq hroot0
      _ = (x ^ (1 / 3 : ℝ)) ^ 3 := by ring
      _ = x := hrootcube
  have hthousand : (1000 : ℝ) * (q : ℝ) ^ 2 ≤ x := by
    linarith
  have hq_small : (q : ℝ) ≤ (1 / 1000 : ℝ) * (x / q) := by
    rw [show (1 / 1000 : ℝ) * (x / q) =
      ((1 / 1000 : ℝ) * x) / q by ring]
    apply (le_div_iff₀ hqpos).2
    nlinarith
  have hsqrtqpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hxypos : 0 < x / (q : ℝ) := div_pos hxpos hqpos
  have hsqrtypos : 0 < Real.sqrt (x / (q : ℝ)) := Real.sqrt_pos.2 hxypos
  have hsqrt4m : Real.sqrt (4000000 : ℝ) = 2000 := by norm_num
  have hsqrt_bound : 2000 * Real.sqrt (q : ℝ) ≤
      Real.sqrt (x / (q : ℝ)) := by
    have hlin : (4000000 : ℝ) * q ≤ x / q := by
      apply (le_div_iff₀ hqpos).2
      nlinarith
    calc
      2000 * Real.sqrt (q : ℝ) =
          Real.sqrt ((4000000 : ℝ) * q) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4000000), hsqrt4m]
      _ ≤ Real.sqrt (x / q) := Real.sqrt_le_sqrt hlin
  have hfar_fraction : x / Real.sqrt (x / (q : ℝ)) ≤
      (1 / 2000 : ℝ) * (x / Real.sqrt q) := by
    have hscaled : 2000 * (x / Real.sqrt (x / (q : ℝ))) ≤
        x / Real.sqrt q := by
      apply (le_div_iff₀ hsqrtqpos).2
      calc
        2000 * (x / Real.sqrt (x / (q : ℝ))) * Real.sqrt q =
            x * (2000 * Real.sqrt q) / Real.sqrt (x / q) := by ring
        _ ≤ x * Real.sqrt (x / q) / Real.sqrt (x / q) := by
          gcongr
        _ = x := by field_simp
    nlinarith
  have hsqrtqU : Real.sqrt (q : ℝ) ≤ Real.sqrt U :=
    Real.sqrt_le_sqrt hUq
  have hsqrtUpos : 0 < Real.sqrt U :=
    lt_of_lt_of_le hsqrtqpos hsqrtqU
  have hU_fraction : x / Real.sqrt U ≤ x / Real.sqrt q :=
    div_le_div_of_nonneg_left hx0 hsqrtqpos hsqrtqU
  have hlogx : Real.log x ≤ Real.log (2 * x) := by
    exact Real.log_le_log hxpos (by nlinarith)
  have hargpos : 0 ≤ Real.log (2 * x / (q : ℝ) ^ 2 + 4) := by
    apply Real.log_nonneg
    have : 0 ≤ 2 * x / (q : ℝ) ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hlogpow3 : Real.log ((q : ℝ) ^ 3) = 3 * Real.log q := by
    rw [Real.log_pow]
    norm_num
  have hlogpow2 : Real.log ((q : ℝ) ^ 2) = 2 * Real.log q := by
    rw [Real.log_pow]
    norm_num
  have htwoUV : 2 * U * V / q + 4 = 2 * x / (q : ℝ) ^ 2 + 4 := by
    calc
      2 * U * V / q + 4 = 2 * (U * V) / q + 4 := by ring
      _ = 2 * x / (q : ℝ) ^ 2 + 4 := by rw [hUVeq]; field_simp
  have hxUV : x / (U * V) = q := by
    rw [hUVeq]
    field_simp
  have hVxU : V * x / U = (q : ℝ) ^ 3 := by
    dsimp [U, V]
    field_simp
  have hxU : x / U = (q : ℝ) ^ 2 := by
    dsimp [U]
    field_simp
  have hsource := exp_sum_estimate_vaughan_modulus_two_source
    x alpha beta U V a q hq4 haq halpha hbeta hU40 hV40 hUx hVx hUV hUV2
  rw [htwoUV, hxUV, hVxU, hxU, hlogpow3, hlogpow2, hUVeq] at hsource
  dsimp [V] at hsource
  have hterm1 :
      0.5 * (x / q) * Real.log x *
          Real.log (2 * x / (q : ℝ) ^ 2 + 4) ≤
        (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4)) := by
    have hxq0 : 0 ≤ x / (q : ℝ) := div_nonneg hx0 hq0
    have hcoef0 : 0 ≤ 0.5 * (x / (q : ℝ)) *
        Real.log (2 * x / (q : ℝ) ^ 2 + 4) := by positivity
    calc
      _ = (0.5 * (x / q) * Real.log (2 * x / (q : ℝ) ^ 2 + 4)) *
          Real.log x := by ring
      _ ≤ (0.5 * (x / q) * Real.log (2 * x / (q : ℝ) ^ 2 + 4)) *
          Real.log (2 * x) := mul_le_mul_of_nonneg_left hlogx hcoef0
      _ = _ := by ring
  have htermI :
      0.89 * (x / q + (5 / 2 : ℝ) * q) *
          (8 + Real.log q) * Real.log (2 * x) ≤
        (x / q) * Real.log (2 * x) * (0.9 * (8 + Real.log q)) := by
    have hxq0 : 0 ≤ x / (q : ℝ) := div_nonneg hx0 hq0
    have hlogfactor : 0 ≤ 8 + Real.log (q : ℝ) := by linarith only [hlogq]
    have hcoef : 0.89 * (x / q + (5 / 2 : ℝ) * q) ≤
        0.9 * (x / q) := by nlinarith only [hq_small, hxq0]
    have hfactor : 0 ≤ (8 + Real.log (q : ℝ)) * Real.log (2 * x) :=
      mul_nonneg hlogfactor hlog2x
    calc
      _ = (0.89 * (x / q + (5 / 2 : ℝ) * q)) *
          ((8 + Real.log q) * Real.log (2 * x)) := by ring
      _ ≤ (0.9 * (x / q)) *
          ((8 + Real.log q) * Real.log (2 * x)) :=
        mul_le_mul_of_nonneg_right hcoef hfactor
      _ = _ := by ring
  have htypeIIa :
      (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
            Real.log q * (3 * Real.log q) ≤
        0.301 * Real.log q ^ 2 * (x / Real.sqrt q) := by
    have hxroot0 : 0 ≤ x / Real.sqrt (q : ℝ) := div_nonneg hx0 (Real.sqrt_nonneg _)
    have hcoef :
        0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q)) ≤
          0.100195 * (x / Real.sqrt q) := by
      nlinarith only [hfar_fraction, hxroot0]
    have hlogsq : 0 ≤ 3 * Real.log (q : ℝ) ^ 2 := by positivity
    calc
      _ = (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) *
            (3 * Real.log q ^ 2) := by ring
      _ ≤ (0.100195 * (x / Real.sqrt q)) *
          (3 * Real.log q ^ 2) := mul_le_mul_of_nonneg_right hcoef hlogsq
      _ = 0.300585 * (x / Real.sqrt q) * Real.log q ^ 2 := by ring
      _ ≤ 0.301 * (x / Real.sqrt q) * Real.log q ^ 2 := by
        gcongr
        norm_num
      _ = _ := by ring
  have htypeIIb :
      (0.55 * (x / Real.sqrt U) +
          0.78 * (x / Real.sqrt q)) * (2 * Real.log q) ≤
        2.66 * Real.log q * (x / Real.sqrt q) := by
    have hxroot0 : 0 ≤ x / Real.sqrt (q : ℝ) := div_nonneg hx0 (Real.sqrt_nonneg _)
    have hcoef : 0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt q) ≤
        1.33 * (x / Real.sqrt q) := by
      nlinarith only [hU_fraction, hxroot0]
    calc
      _ ≤ (1.33 * (x / Real.sqrt q)) * (2 * Real.log q) := by
        gcongr
      _ = _ := by ring
  calc
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
        0.5 * (x / q) * Real.log x *
            Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
          0.89 * (x / q + (5 / 2 : ℝ) * q) *
            (8 + Real.log q) * Real.log (2 * x) +
          (0.1 * (x / Real.sqrt q) +
            0.39 * (x / Real.sqrt (x / q))) *
              Real.log q * (3 * Real.log q) +
          (0.55 * (x / Real.sqrt U) +
            0.78 * (x / Real.sqrt q)) * (2 * Real.log q) := hsource
    _ ≤ (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4)) +
        (x / q) * Real.log (2 * x) * (0.9 * (8 + Real.log q)) +
        0.301 * Real.log q ^ 2 * (x / Real.sqrt q) +
        2.66 * Real.log q * (x / Real.sqrt q) := by
      exact add_le_add (add_le_add (add_le_add hterm1 htermI) htypeIIa) htypeIIb
    _ = (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) := by ring

end TaoFivePrimes
end


-- Source module: Solutions.Sol_TaoFivePrimes_small_q_modulus_two_source_envelope_standalone
section
open TaoFivePrimes

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q)  := by
  exact exp_sum_estimate_small_q_modulus_two_source
    x alpha beta a q hx hq hqx haq halpha hbeta hsmall
end


#print axioms solution
