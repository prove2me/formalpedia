-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_large_q_unit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T12:09:12.734975+00:00
-- url     : https://prove2.me/submissions/9858d619-2b5b-4a32-9680-7475720de65c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_large_q_unit_source_envelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open TaoFivePrimes

set_option maxHeartbeats 800000

namespace TaoFivePrimes

private theorem rpow_pow_three_one_third (v : ℝ) (hv : 0 ≤ v) :
    (v ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = v := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hv]
  norm_num

end TaoFivePrimes

theorem solution (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hlarge : x ^ (2 / 3 : ℝ) ≤ (q : ℝ))
    (ha : a = 1 ∨ a = -1) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      9.73 * (x / (x / q) ^ 2) * Real.log x ^ 2
        + 1.2 * (x / Real.sqrt (x / q)) * Real.log (x / q) *
          (Real.log (x / q) + 2.4) := by
  let w : ℝ := x / q
  let V : ℝ := 1.02 * w
  let U : ℝ := x / V ^ 2
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxnonneg : 0 ≤ x := hxpos.le
  have hqpos_nat : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqpos_nat
  have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
  have hq100 : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hwlo : (100 : ℝ) ≤ w := by
    apply (le_div_iff₀ hqpos).2
    have hc := (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mp hqx
    nlinarith
  have hx13pos : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hx23pos : 0 < x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hx13_nonneg : 0 ≤ x ^ (1 / 3 : ℝ) := hx13pos.le
  have hx_thirds : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hx_two_thirds :
      x ^ (2 / 3 : ℝ) = x ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hbase18 : ((10 : ℝ) ^ 6) ^ (3 : ℕ) ≤ x := by
    norm_num at hx ⊢
    linarith
  have hx13lo : (10 : ℝ) ^ 6 ≤ x ^ (1 / 3 : ℝ) := by
    have hr := Real.rpow_le_rpow (by positivity) hbase18
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [TaoFivePrimes.rpow_pow_three_one_third ((10 : ℝ) ^ 6) (by positivity)] at hr
    exact hr
  have hwle : w ≤ x ^ (1 / 3 : ℝ) := by
    have hd := div_le_div₀ hxnonneg le_rfl hx23pos hlarge
    calc
      w = x / (q : ℝ) := rfl
      _ ≤ x / x ^ (2 / 3 : ℝ) := hd
      _ = x ^ (1 / 3 : ℝ) := by
        apply (div_eq_iff hx23pos.ne').2
        nlinarith [hx_thirds]
  have hwcube : w ^ 3 ≤ x := by
    calc
      w ^ 3 ≤ (x ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hwpos.le hwle 3
      _ = x := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hxnonneg]
        norm_num
  have hVdef : V = 1.02 * x / q := by dsimp [V, w]; ring
  have hUdef : U = x / V ^ 2 := rfl
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hV40 : (40 : ℝ) ≤ V := by dsimp [V]; nlinarith
  have hVone : (1 : ℝ) < V := lt_of_lt_of_le (by norm_num) hV40
  have hVx : V < x := by
    have hw_x100 : w ≤ x / 100 := by
      dsimp [w]
      exact div_le_div₀ hxnonneg le_rfl (by norm_num) hq100
    dsimp [V]
    nlinarith
  have hV2pos : 0 < V ^ 2 := sq_pos_of_pos hVpos
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU40 : (40 : ℝ) ≤ U := by
    apply (le_div_iff₀ hV2pos).2
    change 40 * V ^ 2 ≤ x
    calc
      40 * V ^ 2 = (40 * 1.02 ^ 2) * w ^ 2 := by dsimp [V]; ring
      _ ≤ w * w ^ 2 := by
        gcongr
        nlinarith
      _ = w ^ 3 := by ring
      _ ≤ x := hwcube
  have hUx : U < x := by
    have hV2one : (1 : ℝ) < V ^ 2 := by nlinarith [sq_nonneg (V - 1)]
    dsimp [U]
    exact div_lt_self hxpos hV2one
  have hUV2eq : U * V ^ 2 = x := by
    dsimp [U]
    field_simp
  have hUV2 : x ≤ U * V ^ 2 := hUV2eq.ge
  have hUVeq : U * V = (q : ℝ) / 1.02 := by
    dsimp [U, V, w]
    field_simp
  have hUV : U * V ≤ x / 4 := by
    rw [hUVeq]
    calc
      (q : ℝ) / 1.02 ≤ (x / 100) / 1.02 :=
        div_le_div_of_nonneg_right hqx (by norm_num)
      _ ≤ x / 4 := by norm_num; nlinarith
  have hUVq : U * V < (q : ℝ) - 1 := by
    rw [hUVeq]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1.02)).2
    nlinarith
  have haunit : a.natAbs = 1 := by
    rcases ha with rfl | rfl <;> norm_num
  have hsource :=
    TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope
      x alpha beta U V a q q0 hx hq hqx haq haunit halpha hbeta hq0 hlarge
      hUdef hVdef hU40 hV40 hUx hVx hUV hUV2 hUVq

  have hlogw_nonneg : 0 ≤ Real.log w := Real.log_nonneg (by linarith)
  have hlogV_nonneg : 0 ≤ Real.log V := Real.log_nonneg hVone.le
  have hexp_four_lt_w : Real.exp 4 < w := by
    calc
      Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < (3 : ℝ) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ < w := by norm_num; linarith
  have hlogw_four : (4 : ℝ) ≤ Real.log w :=
    (Real.le_log_iff_exp_le hwpos).2 hexp_four_lt_w.le
  have hlog102 : Real.log (1.02 : ℝ) ≤ 0.02 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.02)
    norm_num at h ⊢
    exact h
  have hlogV : Real.log V = Real.log 1.02 + Real.log w := by
    dsimp [V]
    rw [Real.log_mul (by norm_num : (1.02 : ℝ) ≠ 0) hwpos.ne']

  have hpi_sq : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 2
  have hcoef_pi : (96 : ℝ) / Real.pi ^ 2 ≤ 9.73 := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    calc
      (96 : ℝ) ≤ 9.73 * (3.1415 : ℝ) ^ 2 := by norm_num
      _ ≤ 9.73 * Real.pi ^ 2 := by gcongr
  have hargpos : 0 < 4 * Real.exp 1 * (q : ℝ) / Real.pi := by positivity
  have hx4pos : 0 < x / 4 := by positivity
  have harg_le : 4 * Real.exp 1 * (q : ℝ) / Real.pi ≤ x / 4 := by
    apply (div_le_iff₀ Real.pi_pos).2
    calc
      4 * Real.exp 1 * (q : ℝ) ≤ 12 * (q : ℝ) := by
        have h4e : 4 * Real.exp 1 ≤ (12 : ℝ) := by
          nlinarith [Real.exp_one_lt_three]
        exact mul_le_mul_of_nonneg_right h4e hqnonneg
      _ ≤ 12 * (x / 100) := by gcongr
      _ ≤ (x / 4) * Real.pi := by
        have hp := Real.pi_gt_three.le
        nlinarith
  have hlogarg :
      Real.log (4 * Real.exp 1 * (q : ℝ) / Real.pi) ≤ Real.log (x / 4) :=
    Real.log_le_log hargpos harg_le
  have hlog4x_nonneg : 0 ≤ Real.log (4 * x) :=
    Real.log_nonneg (by nlinarith)
  have hlogx4_nonneg : 0 ≤ Real.log (x / 4) :=
    Real.log_nonneg (by nlinarith)
  have hlogarg_nonneg :
      0 ≤ Real.log (4 * Real.exp 1 * (q : ℝ) / Real.pi) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ Real.pi_pos).2
    calc
      1 * Real.pi ≤ 4 := by simpa using Real.pi_lt_four.le
      _ ≤ 4 * Real.exp 1 := by
        have heone : (1 : ℝ) ≤ Real.exp 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_monotone (by norm_num)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left heone
          (by norm_num : (0 : ℝ) ≤ 4)
      _ ≤ 4 * Real.exp 1 * (q : ℝ) := by
        have hqone : (1 : ℝ) ≤ (q : ℝ) := by linarith
        simpa using mul_le_mul_of_nonneg_left hqone
          (show 0 ≤ 4 * Real.exp 1 by positivity)
  have hlog_product :
      Real.log (4 * x) * Real.log (4 * Real.exp 1 * (q : ℝ) / Real.pi) ≤
        Real.log x ^ 2 := by
    calc
      Real.log (4 * x) * Real.log (4 * Real.exp 1 * (q : ℝ) / Real.pi) ≤
          Real.log (4 * x) * Real.log (x / 4) :=
        mul_le_mul_of_nonneg_left hlogarg hlog4x_nonneg
      _ = (Real.log 4 + Real.log x) * (Real.log x - Real.log 4) := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hxpos.ne',
          Real.log_div hxpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
      _ = Real.log x ^ 2 - Real.log 4 ^ 2 := by ring
      _ ≤ Real.log x ^ 2 := sub_le_self _ (sq_nonneg _)
  have hterm1 :
      (96 / Real.pi ^ 2) * (x / w ^ 2) * Real.log (4 * x) *
          Real.log (4 * Real.exp 1 * q / Real.pi) ≤
        9.73 * (x / w ^ 2) * Real.log x ^ 2 := by
    have hxw_nonneg : 0 ≤ x / w ^ 2 := by positivity
    have hlogs_nonneg : 0 ≤ Real.log (4 * x) *
        Real.log (4 * Real.exp 1 * (q : ℝ) / Real.pi) :=
      mul_nonneg hlog4x_nonneg hlogarg_nonneg
    have hcoeffstep :
        (96 / Real.pi ^ 2) * (x / w ^ 2) *
            (Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi)) ≤
          9.73 * (x / w ^ 2) *
            (Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef_pi hxw_nonneg) hlogs_nonneg
    calc
      (96 / Real.pi ^ 2) * (x / w ^ 2) * Real.log (4 * x) *
          Real.log (4 * Real.exp 1 * q / Real.pi) =
        (96 / Real.pi ^ 2) * (x / w ^ 2) *
          (Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi)) := by ring
      _ ≤
        9.73 * (x / w ^ 2) *
          (Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi)) := hcoeffstep
      _ ≤ 9.73 * (x / w ^ 2) * Real.log x ^ 2 :=
        mul_le_mul_of_nonneg_left hlog_product
          (mul_nonneg (by norm_num) hxw_nonneg)

  have hmillion_w_le_q : (10 : ℝ) ^ 6 * w ≤ (q : ℝ) := by
    calc
      (10 : ℝ) ^ 6 * w ≤ x ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ) := by
        gcongr
      _ = x ^ (2 / 3 : ℝ) := hx_two_thirds.symm
      _ ≤ (q : ℝ) := hlarge
  have hsqrt_million : Real.sqrt ((10 : ℝ) ^ 6) = 1000 := by
    rw [show (10 : ℝ) ^ 6 = 1000000 by norm_num]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrtq_bound : 1000 * Real.sqrt w ≤ Real.sqrt (q : ℝ) := by
    calc
      1000 * Real.sqrt w = Real.sqrt ((10 : ℝ) ^ 6 * w) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 6), hsqrt_million]
      _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hmillion_w_le_q
  have hsqrtwpos : 0 < Real.sqrt w := Real.sqrt_pos.2 hwpos
  have hsqrtqpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hxq_bound :
      x / Real.sqrt (q : ℝ) ≤ 0.001 * (x / Real.sqrt w) := by
    calc
      x / Real.sqrt (q : ℝ) ≤ x / (1000 * Real.sqrt w) :=
        div_le_div₀ hxnonneg le_rfl (by positivity) hsqrtq_bound
      _ = 0.001 * (x / Real.sqrt w) := by ring
  have hterm2 :
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt w)) * 3 *
          Real.log V ^ 2 ≤
        1.19 * (x / Real.sqrt w) * Real.log V ^ 2 := by
    have hxsw_nonneg : 0 ≤ x / Real.sqrt w := by positivity
    calc
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt w)) * 3 *
          Real.log V ^ 2 ≤
        (0.1 * (0.001 * (x / Real.sqrt w)) +
          0.39 * (x / Real.sqrt w)) * 3 * Real.log V ^ 2 := by gcongr
      _ = 1.1703 * (x / Real.sqrt w) * Real.log V ^ 2 := by ring
      _ ≤ 1.19 * (x / Real.sqrt w) * Real.log V ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) hxsw_nonneg) (sq_nonneg _)

  have hw_le_scaledU : w ≤ 1.02 ^ 2 * U := by
    have hmul : w * w ^ 2 ≤ (1.02 ^ 2 * U) * w ^ 2 := by
      calc
        w * w ^ 2 = w ^ 3 := by ring
        _ ≤ x := hwcube
        _ = U * V ^ 2 := hUV2eq.symm
        _ = (1.02 ^ 2 * U) * w ^ 2 := by
          rw [show V = 1.02 * w by rfl]
          ring
    exact le_of_mul_le_mul_right hmul (pow_pos hwpos 2)
  have hsqrtUpos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
  have hsqrtVpos : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
  have hswU : Real.sqrt w ≤ 1.02 * Real.sqrt U := by
    have hw_sq := Real.sq_sqrt hwpos.le
    have hU_sq := Real.sq_sqrt hUpos.le
    have hsw := Real.sqrt_nonneg w
    have hsU := Real.sqrt_nonneg U
    nlinarith only [hw_sq, hU_sq, hsw, hsU, hw_le_scaledU]
  have hxU_bound :
      x / Real.sqrt U ≤ 1.02 * (x / Real.sqrt w) := by
    apply (div_le_iff₀ hsqrtUpos).2
    rw [show 1.02 * (x / Real.sqrt w) * Real.sqrt U =
      (1.02 * x * Real.sqrt U) / Real.sqrt w by ring]
    apply (le_div_iff₀ hsqrtwpos).2
    calc
      x * Real.sqrt w ≤ x * (1.02 * Real.sqrt U) :=
        mul_le_mul_of_nonneg_left hswU hxnonneg
      _ = 1.02 * x * Real.sqrt U := by ring
  have hsqrt102 : (1.009 : ℝ) ^ 2 ≤ 1.02 := by norm_num
  have hswV : 1.009 * Real.sqrt w ≤ Real.sqrt V := by
    have hw_sq := Real.sq_sqrt hwpos.le
    have hscaled := mul_le_mul_of_nonneg_right hsqrt102 hwpos.le
    apply Real.le_sqrt_of_sq_le
    calc
      (1.009 * Real.sqrt w) ^ 2 = 1.009 ^ 2 * w := by
        rw [mul_pow, hw_sq]
      _ ≤ 1.02 * w := hscaled
      _ = V := by rfl
  have hxV_bound :
      x / Real.sqrt V ≤ (1 / 1.009 : ℝ) * (x / Real.sqrt w) := by
    calc
      x / Real.sqrt V ≤ x / (1.009 * Real.sqrt w) :=
        div_le_div₀ hxnonneg le_rfl (by positivity) hswV
      _ = (1 / 1.009 : ℝ) * (x / Real.sqrt w) := by ring
  have hterm3 :
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) * 2 *
          Real.log V ≤
        2.67 * (x / Real.sqrt w) * Real.log V := by
    have hxsw_nonneg : 0 ≤ x / Real.sqrt w := by positivity
    have hcoef3 :
        (0.55 * 1.02 + 0.78 * (1 / 1.009 : ℝ)) * 2 ≤ 2.67 := by
      norm_num
    calc
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) * 2 *
          Real.log V ≤
        (0.55 * (1.02 * (x / Real.sqrt w)) +
          0.78 * ((1 / 1.009 : ℝ) * (x / Real.sqrt w))) * 2 *
            Real.log V := by gcongr
      _ = ((0.55 * 1.02 + 0.78 * (1 / 1.009 : ℝ)) * 2) *
          (x / Real.sqrt w) * Real.log V := by ring
      _ ≤ 2.67 * (x / Real.sqrt w) * Real.log V :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef3 hxsw_nonneg) hlogV_nonneg

  have hterms23 :
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt w)) * 3 *
          Real.log V ^ 2 +
        (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) * 2 *
          Real.log V ≤
        1.199 * (x / Real.sqrt w) * Real.log w * (Real.log w + 2.4) := by
    have hxsw_nonneg : 0 ≤ x / Real.sqrt w := by positivity
    have hsource23 :
        1.19 * (x / Real.sqrt w) * Real.log V ^ 2 +
            2.67 * (x / Real.sqrt w) * Real.log V ≤
          1.19 * (x / Real.sqrt w) * Real.log V * (Real.log V + 2.3) := by
      have hlinear :
          2.67 * (x / Real.sqrt w) * Real.log V ≤
            (1.19 * 2.3) * (x / Real.sqrt w) * Real.log V :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) hxsw_nonneg) hlogV_nonneg
      calc
        1.19 * (x / Real.sqrt w) * Real.log V ^ 2 +
            2.67 * (x / Real.sqrt w) * Real.log V ≤
          1.19 * (x / Real.sqrt w) * Real.log V ^ 2 +
            (1.19 * 2.3) * (x / Real.sqrt w) * Real.log V :=
          add_le_add_right hlinear _
        _ = 1.19 * (x / Real.sqrt w) * Real.log V *
            (Real.log V + 2.3) := by ring
    have hfac1 : 1.19 * Real.log V ≤ 1.196 * Real.log w := by
      rw [hlogV]
      linarith only [hlog102, hlogw_four]
    have hfac2 : Real.log V + 2.3 ≤ Real.log w + 2.32 := by
      rw [hlogV]
      linarith only [hlog102]
    have hcompare :
        1.19 * (x / Real.sqrt w) * Real.log V * (Real.log V + 2.3) ≤
          1.199 * (x / Real.sqrt w) * Real.log w * (Real.log w + 2.4) := by
      calc
        1.19 * (x / Real.sqrt w) * Real.log V * (Real.log V + 2.3) =
            (x / Real.sqrt w) * (1.19 * Real.log V) * (Real.log V + 2.3) := by ring
        _ ≤ (x / Real.sqrt w) * (1.196 * Real.log w) *
            (Real.log w + 2.32) := by gcongr
        _ ≤ (x / Real.sqrt w) * (1.199 * Real.log w) *
            (Real.log w + 2.4) := by gcongr <;> norm_num
        _ = 1.199 * (x / Real.sqrt w) * Real.log w *
            (Real.log w + 2.4) := by ring
    linarith only [hterm2, hterm3, hsource23, hcompare]

  have hmillion_w_le_x : (10 : ℝ) ^ 6 * w ≤ x := by
    have hx13one : (1 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
      norm_num at hx13lo ⊢
      linarith
    have hx23le : x ^ (2 / 3 : ℝ) ≤ x := by
      calc
        x ^ (2 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) :=
          le_mul_of_one_le_left hx23pos.le hx13one
        _ = x := hx_thirds
    calc
      (10 : ℝ) ^ 6 * w ≤ x ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ) := by
        exact mul_le_mul hx13lo hwle (by positivity) hx13_nonneg
      _ = x ^ (2 / 3 : ℝ) := hx_two_thirds.symm
      _ ≤ x := hx23le
  have hsqrtxnonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrtx_bound : 1000 * Real.sqrt w ≤ Real.sqrt x := by
    calc
      1000 * Real.sqrt w = Real.sqrt ((10 : ℝ) ^ 6 * w) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ 6), hsqrt_million]
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hmillion_w_le_x
  have hxw_scale : 1000 * Real.sqrt x ≤ x / Real.sqrt w := by
    apply (le_div_iff₀ hsqrtwpos).2
    calc
      1000 * Real.sqrt x * Real.sqrt w =
          Real.sqrt x * (1000 * Real.sqrt w) := by ring
      _ ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hsqrtx_bound hsqrtxnonneg
      _ = x := Real.mul_self_sqrt hxnonneg
  have hlogprod : (25.6 : ℝ) ≤ Real.log w * (Real.log w + 2.4) := by
    nlinarith only [hlogw_four]
  have hsieve :
      20.16 * Real.sqrt x ≤
        0.001 * (x / Real.sqrt w) * Real.log w * (Real.log w + 2.4) := by
    calc
      20.16 * Real.sqrt x ≤ 25.6 * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (by norm_num) hsqrtxnonneg
      _ = 0.001 * (1000 * Real.sqrt x) * 25.6 := by ring
      _ ≤ 0.001 * (x / Real.sqrt w) *
          (Real.log w * (Real.log w + 2.4)) := by gcongr
      _ = 0.001 * (x / Real.sqrt w) * Real.log w *
          (Real.log w + 2.4) := by ring
  have htail :
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt w)) * 3 *
          Real.log V ^ 2 +
        (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) * 2 *
          Real.log V + 20.16 * Real.sqrt x ≤
        1.2 * (x / Real.sqrt w) * Real.log w * (Real.log w + 2.4) := by
    linarith only [hterms23, hsieve]
  change ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      9.73 * (x / w ^ 2) * Real.log x ^ 2 +
        1.2 * (x / Real.sqrt w) * Real.log w * (Real.log w + 2.4)
  linarith only [hsource, hterm1, htail]

#print axioms solution
