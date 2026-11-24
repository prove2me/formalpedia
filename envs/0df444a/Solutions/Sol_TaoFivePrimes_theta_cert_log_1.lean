-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_log_1
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T12:54:53.275778+00:00
-- url     : https://prove2.me/submissions/8200f435-a111-4121-9279-b5cd54071f26

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

lemma clb_log_2 : ((clbZ 2 : ℕ) : ℝ) < Real.log 2 * 10 ^ 4 := by
  have hM : ((clbZ 2 : ℕ) : ℝ) = ((0 : ℝ) + 0.6931) * 10 ^ 4 := by
    rw [show clbZ 2 = 6931 by decide]
    norm_num
  rw [hM]
  have hexp : (0 : ℝ) + 0.6931 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    have hm : Real.exp (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 0 := by
      rw [show (0 : ℝ) = (0 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 0
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6931)
      (by norm_num : (0.6931 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((0 : ℝ) + 0.6931) ≤ (2.7182818286 : ℝ) ^ 0 * Real.exp 0.6931 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6931)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 0)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((0 : ℝ) + 0.6931) * 10 ^ 4 < Real.log 2 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_3 : ((clbZ 3 : ℕ) : ℝ) < Real.log 3 * 10 ^ 4 := by
  have hM : ((clbZ 3 : ℕ) : ℝ) = ((1 : ℝ) + 0.0986) * 10 ^ 4 := by
    rw [show clbZ 3 = 10986 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.0986 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0986)
      (by norm_num : (0.0986 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.0986) ≤ (2.7182818286 : ℝ) ^ 1 * Real.exp 0.0986 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0986)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.0986) * 10 ^ 4 < Real.log 3 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_5 : ((clbZ 5 : ℕ) : ℝ) < Real.log 5 * 10 ^ 4 := by
  have hM : ((clbZ 5 : ℕ) : ℝ) = ((1 : ℝ) + 0.6094) * 10 ^ 4 := by
    rw [show clbZ 5 = 16094 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.6094 < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6094)
      (by norm_num : (0.6094 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.6094) ≤ (2.7182818286 : ℝ) ^ 1 * Real.exp 0.6094 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6094)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.6094) * 10 ^ 4 < Real.log 5 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_7 : ((clbZ 7 : ℕ) : ℝ) < Real.log 7 * 10 ^ 4 := by
  have hM : ((clbZ 7 : ℕ) : ℝ) = ((1 : ℝ) + 0.9459) * 10 ^ 4 := by
    rw [show clbZ 7 = 19459 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.9459 < Real.log 7 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 7)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9459)
      (by norm_num : (0.9459 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.9459) ≤ (2.7182818286 : ℝ) ^ 1 * Real.exp 0.9459 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9459)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.9459) * 10 ^ 4 < Real.log 7 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_11 : ((clbZ 11 : ℕ) : ℝ) < Real.log 11 * 10 ^ 4 := by
  have hM : ((clbZ 11 : ℕ) : ℝ) = ((2 : ℝ) + 0.3978) * 10 ^ 4 := by
    rw [show clbZ 11 = 23978 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.3978 < Real.log 11 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 11)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3978)
      (by norm_num : (0.3978 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.3978) ≤ (2.7182818286 : ℝ) ^ 2 * Real.exp 0.3978 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3978)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.3978) * 10 ^ 4 < Real.log 11 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_13 : ((clbZ 13 : ℕ) : ℝ) < Real.log 13 * 10 ^ 4 := by
  have hM : ((clbZ 13 : ℕ) : ℝ) = ((2 : ℝ) + 0.5649) * 10 ^ 4 := by
    rw [show clbZ 13 = 25649 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.5649 < Real.log 13 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 13)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5649)
      (by norm_num : (0.5649 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.5649) ≤ (2.7182818286 : ℝ) ^ 2 * Real.exp 0.5649 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5649)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.5649) * 10 ^ 4 < Real.log 13 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_17 : ((clbZ 17 : ℕ) : ℝ) < Real.log 17 * 10 ^ 4 := by
  have hM : ((clbZ 17 : ℕ) : ℝ) = ((2 : ℝ) + 0.8332) * 10 ^ 4 := by
    rw [show clbZ 17 = 28332 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.8332 < Real.log 17 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 17)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8332)
      (by norm_num : (0.8332 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.8332) ≤ (2.7182818286 : ℝ) ^ 2 * Real.exp 0.8332 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8332)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.8332) * 10 ^ 4 < Real.log 17 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_19 : ((clbZ 19 : ℕ) : ℝ) < Real.log 19 * 10 ^ 4 := by
  have hM : ((clbZ 19 : ℕ) : ℝ) = ((2 : ℝ) + 0.9444) * 10 ^ 4 := by
    rw [show clbZ 19 = 29444 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.9444 < Real.log 19 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 19)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9444)
      (by norm_num : (0.9444 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.9444) ≤ (2.7182818286 : ℝ) ^ 2 * Real.exp 0.9444 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9444)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.9444) * 10 ^ 4 < Real.log 19 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_23 : ((clbZ 23 : ℕ) : ℝ) < Real.log 23 * 10 ^ 4 := by
  have hM : ((clbZ 23 : ℕ) : ℝ) = ((3 : ℝ) + 0.1354) * 10 ^ 4 := by
    rw [show clbZ 23 = 31354 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.1354 < Real.log 23 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 23)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1354)
      (by norm_num : (0.1354 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.1354) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.1354 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1354)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.1354) * 10 ^ 4 < Real.log 23 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_29 : ((clbZ 29 : ℕ) : ℝ) < Real.log 29 * 10 ^ 4 := by
  have hM : ((clbZ 29 : ℕ) : ℝ) = ((3 : ℝ) + 0.3672) * 10 ^ 4 := by
    rw [show clbZ 29 = 33672 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.3672 < Real.log 29 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 29)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3672)
      (by norm_num : (0.3672 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.3672) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.3672 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3672)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.3672) * 10 ^ 4 < Real.log 29 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_31 : ((clbZ 31 : ℕ) : ℝ) < Real.log 31 * 10 ^ 4 := by
  have hM : ((clbZ 31 : ℕ) : ℝ) = ((3 : ℝ) + 0.4339) * 10 ^ 4 := by
    rw [show clbZ 31 = 34339 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.4339 < Real.log 31 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 31)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4339)
      (by norm_num : (0.4339 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.4339) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.4339 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4339)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.4339) * 10 ^ 4 < Real.log 31 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_37 : ((clbZ 37 : ℕ) : ℝ) < Real.log 37 * 10 ^ 4 := by
  have hM : ((clbZ 37 : ℕ) : ℝ) = ((3 : ℝ) + 0.6109) * 10 ^ 4 := by
    rw [show clbZ 37 = 36109 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.6109 < Real.log 37 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 37)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6109)
      (by norm_num : (0.6109 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.6109) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.6109 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6109)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.6109) * 10 ^ 4 < Real.log 37 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_41 : ((clbZ 41 : ℕ) : ℝ) < Real.log 41 * 10 ^ 4 := by
  have hM : ((clbZ 41 : ℕ) : ℝ) = ((3 : ℝ) + 0.7135) * 10 ^ 4 := by
    rw [show clbZ 41 = 37135 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.7135 < Real.log 41 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 41)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7135)
      (by norm_num : (0.7135 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.7135) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.7135 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7135)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.7135) * 10 ^ 4 < Real.log 41 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_43 : ((clbZ 43 : ℕ) : ℝ) < Real.log 43 * 10 ^ 4 := by
  have hM : ((clbZ 43 : ℕ) : ℝ) = ((3 : ℝ) + 0.7612) * 10 ^ 4 := by
    rw [show clbZ 43 = 37612 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.7612 < Real.log 43 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 43)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7612)
      (by norm_num : (0.7612 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.7612) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.7612 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7612)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.7612) * 10 ^ 4 < Real.log 43 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_47 : ((clbZ 47 : ℕ) : ℝ) < Real.log 47 * 10 ^ 4 := by
  have hM : ((clbZ 47 : ℕ) : ℝ) = ((3 : ℝ) + 0.8501) * 10 ^ 4 := by
    rw [show clbZ 47 = 38501 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.8501 < Real.log 47 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 47)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8501)
      (by norm_num : (0.8501 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.8501) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.8501 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8501)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.8501) * 10 ^ 4 < Real.log 47 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_53 : ((clbZ 53 : ℕ) : ℝ) < Real.log 53 * 10 ^ 4 := by
  have hM : ((clbZ 53 : ℕ) : ℝ) = ((3 : ℝ) + 0.9702) * 10 ^ 4 := by
    rw [show clbZ 53 = 39702 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.9702 < Real.log 53 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 53)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9702)
      (by norm_num : (0.9702 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.9702) ≤ (2.7182818286 : ℝ) ^ 3 * Real.exp 0.9702 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9702)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.9702) * 10 ^ 4 < Real.log 53 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_59 : ((clbZ 59 : ℕ) : ℝ) < Real.log 59 * 10 ^ 4 := by
  have hM : ((clbZ 59 : ℕ) : ℝ) = ((4 : ℝ) + 0.0775) * 10 ^ 4 := by
    rw [show clbZ 59 = 40775 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.0775 < Real.log 59 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 59)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0775)
      (by norm_num : (0.0775 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.0775) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.0775 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0775)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.0775) * 10 ^ 4 < Real.log 59 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_61 : ((clbZ 61 : ℕ) : ℝ) < Real.log 61 * 10 ^ 4 := by
  have hM : ((clbZ 61 : ℕ) : ℝ) = ((4 : ℝ) + 0.1108) * 10 ^ 4 := by
    rw [show clbZ 61 = 41108 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.1108 < Real.log 61 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 61)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1108)
      (by norm_num : (0.1108 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.1108) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.1108 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1108)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.1108) * 10 ^ 4 < Real.log 61 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_67 : ((clbZ 67 : ℕ) : ℝ) < Real.log 67 * 10 ^ 4 := by
  have hM : ((clbZ 67 : ℕ) : ℝ) = ((4 : ℝ) + 0.2046) * 10 ^ 4 := by
    rw [show clbZ 67 = 42046 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.2046 < Real.log 67 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 67)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2046)
      (by norm_num : (0.2046 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.2046) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.2046 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2046)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.2046) * 10 ^ 4 < Real.log 67 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_71 : ((clbZ 71 : ℕ) : ℝ) < Real.log 71 * 10 ^ 4 := by
  have hM : ((clbZ 71 : ℕ) : ℝ) = ((4 : ℝ) + 0.2626) * 10 ^ 4 := by
    rw [show clbZ 71 = 42626 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.2626 < Real.log 71 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 71)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2626)
      (by norm_num : (0.2626 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.2626) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.2626 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2626)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.2626) * 10 ^ 4 < Real.log 71 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_73 : ((clbZ 73 : ℕ) : ℝ) < Real.log 73 * 10 ^ 4 := by
  have hM : ((clbZ 73 : ℕ) : ℝ) = ((4 : ℝ) + 0.2904) * 10 ^ 4 := by
    rw [show clbZ 73 = 42904 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.2904 < Real.log 73 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 73)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2904)
      (by norm_num : (0.2904 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.2904) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.2904 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2904)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.2904) * 10 ^ 4 < Real.log 73 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_79 : ((clbZ 79 : ℕ) : ℝ) < Real.log 79 * 10 ^ 4 := by
  have hM : ((clbZ 79 : ℕ) : ℝ) = ((4 : ℝ) + 0.3694) * 10 ^ 4 := by
    rw [show clbZ 79 = 43694 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.3694 < Real.log 79 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 79)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3694)
      (by norm_num : (0.3694 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.3694) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.3694 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3694)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.3694) * 10 ^ 4 < Real.log 79 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_83 : ((clbZ 83 : ℕ) : ℝ) < Real.log 83 * 10 ^ 4 := by
  have hM : ((clbZ 83 : ℕ) : ℝ) = ((4 : ℝ) + 0.4188) * 10 ^ 4 := by
    rw [show clbZ 83 = 44188 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.4188 < Real.log 83 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 83)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4188)
      (by norm_num : (0.4188 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.4188) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.4188 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4188)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.4188) * 10 ^ 4 < Real.log 83 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_89 : ((clbZ 89 : ℕ) : ℝ) < Real.log 89 * 10 ^ 4 := by
  have hM : ((clbZ 89 : ℕ) : ℝ) = ((4 : ℝ) + 0.4886) * 10 ^ 4 := by
    rw [show clbZ 89 = 44886 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.4886 < Real.log 89 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 89)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4886)
      (by norm_num : (0.4886 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.4886) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.4886 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4886)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.4886) * 10 ^ 4 < Real.log 89 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_97 : ((clbZ 97 : ℕ) : ℝ) < Real.log 97 * 10 ^ 4 := by
  have hM : ((clbZ 97 : ℕ) : ℝ) = ((4 : ℝ) + 0.5747) * 10 ^ 4 := by
    rw [show clbZ 97 = 45747 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.5747 < Real.log 97 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 97)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5747)
      (by norm_num : (0.5747 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.5747) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.5747 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5747)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.5747) * 10 ^ 4 < Real.log 97 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_101 : ((clbZ 101 : ℕ) : ℝ) < Real.log 101 * 10 ^ 4 := by
  have hM : ((clbZ 101 : ℕ) : ℝ) = ((4 : ℝ) + 0.6151) * 10 ^ 4 := by
    rw [show clbZ 101 = 46151 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.6151 < Real.log 101 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 101)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6151)
      (by norm_num : (0.6151 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.6151) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.6151 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6151)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.6151) * 10 ^ 4 < Real.log 101 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_103 : ((clbZ 103 : ℕ) : ℝ) < Real.log 103 * 10 ^ 4 := by
  have hM : ((clbZ 103 : ℕ) : ℝ) = ((4 : ℝ) + 0.6347) * 10 ^ 4 := by
    rw [show clbZ 103 = 46347 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.6347 < Real.log 103 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 103)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6347)
      (by norm_num : (0.6347 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.6347) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.6347 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6347)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.6347) * 10 ^ 4 < Real.log 103 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_107 : ((clbZ 107 : ℕ) : ℝ) < Real.log 107 * 10 ^ 4 := by
  have hM : ((clbZ 107 : ℕ) : ℝ) = ((4 : ℝ) + 0.6728) * 10 ^ 4 := by
    rw [show clbZ 107 = 46728 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.6728 < Real.log 107 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 107)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6728)
      (by norm_num : (0.6728 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.6728) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.6728 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6728)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.6728) * 10 ^ 4 < Real.log 107 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_109 : ((clbZ 109 : ℕ) : ℝ) < Real.log 109 * 10 ^ 4 := by
  have hM : ((clbZ 109 : ℕ) : ℝ) = ((4 : ℝ) + 0.6913) * 10 ^ 4 := by
    rw [show clbZ 109 = 46913 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.6913 < Real.log 109 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 109)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6913)
      (by norm_num : (0.6913 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.6913) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.6913 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6913)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.6913) * 10 ^ 4 < Real.log 109 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_113 : ((clbZ 113 : ℕ) : ℝ) < Real.log 113 * 10 ^ 4 := by
  have hM : ((clbZ 113 : ℕ) : ℝ) = ((4 : ℝ) + 0.7273) * 10 ^ 4 := by
    rw [show clbZ 113 = 47273 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.7273 < Real.log 113 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 113)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7273)
      (by norm_num : (0.7273 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.7273) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.7273 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7273)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.7273) * 10 ^ 4 < Real.log 113 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_127 : ((clbZ 127 : ℕ) : ℝ) < Real.log 127 * 10 ^ 4 := by
  have hM : ((clbZ 127 : ℕ) : ℝ) = ((4 : ℝ) + 0.8441) * 10 ^ 4 := by
    rw [show clbZ 127 = 48441 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.8441 < Real.log 127 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 127)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8441)
      (by norm_num : (0.8441 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.8441) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.8441 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8441)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.8441) * 10 ^ 4 < Real.log 127 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_131 : ((clbZ 131 : ℕ) : ℝ) < Real.log 131 * 10 ^ 4 := by
  have hM : ((clbZ 131 : ℕ) : ℝ) = ((4 : ℝ) + 0.8751) * 10 ^ 4 := by
    rw [show clbZ 131 = 48751 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.8751 < Real.log 131 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 131)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8751)
      (by norm_num : (0.8751 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.8751) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.8751 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8751)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.8751) * 10 ^ 4 < Real.log 131 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_137 : ((clbZ 137 : ℕ) : ℝ) < Real.log 137 * 10 ^ 4 := by
  have hM : ((clbZ 137 : ℕ) : ℝ) = ((4 : ℝ) + 0.9199) * 10 ^ 4 := by
    rw [show clbZ 137 = 49199 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.9199 < Real.log 137 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 137)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9199)
      (by norm_num : (0.9199 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.9199) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.9199 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9199)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.9199) * 10 ^ 4 < Real.log 137 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_139 : ((clbZ 139 : ℕ) : ℝ) < Real.log 139 * 10 ^ 4 := by
  have hM : ((clbZ 139 : ℕ) : ℝ) = ((4 : ℝ) + 0.9344) * 10 ^ 4 := by
    rw [show clbZ 139 = 49344 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.9344 < Real.log 139 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 139)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9344)
      (by norm_num : (0.9344 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.9344) ≤ (2.7182818286 : ℝ) ^ 4 * Real.exp 0.9344 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9344)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.9344) * 10 ^ 4 < Real.log 139 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_149 : ((clbZ 149 : ℕ) : ℝ) < Real.log 149 * 10 ^ 4 := by
  have hM : ((clbZ 149 : ℕ) : ℝ) = ((5 : ℝ) + 0.0039) * 10 ^ 4 := by
    rw [show clbZ 149 = 50039 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.0039 < Real.log 149 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 149)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0039)
      (by norm_num : (0.0039 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.0039) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.0039 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0039)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.0039) * 10 ^ 4 < Real.log 149 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_151 : ((clbZ 151 : ℕ) : ℝ) < Real.log 151 * 10 ^ 4 := by
  have hM : ((clbZ 151 : ℕ) : ℝ) = ((5 : ℝ) + 0.0172) * 10 ^ 4 := by
    rw [show clbZ 151 = 50172 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.0172 < Real.log 151 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 151)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0172)
      (by norm_num : (0.0172 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.0172) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.0172 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0172)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.0172) * 10 ^ 4 < Real.log 151 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_157 : ((clbZ 157 : ℕ) : ℝ) < Real.log 157 * 10 ^ 4 := by
  have hM : ((clbZ 157 : ℕ) : ℝ) = ((5 : ℝ) + 0.0562) * 10 ^ 4 := by
    rw [show clbZ 157 = 50562 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.0562 < Real.log 157 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 157)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0562)
      (by norm_num : (0.0562 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.0562) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.0562 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0562)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.0562) * 10 ^ 4 < Real.log 157 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_163 : ((clbZ 163 : ℕ) : ℝ) < Real.log 163 * 10 ^ 4 := by
  have hM : ((clbZ 163 : ℕ) : ℝ) = ((5 : ℝ) + 0.0937) * 10 ^ 4 := by
    rw [show clbZ 163 = 50937 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.0937 < Real.log 163 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 163)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0937)
      (by norm_num : (0.0937 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.0937) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.0937 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0937)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.0937) * 10 ^ 4 < Real.log 163 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_167 : ((clbZ 167 : ℕ) : ℝ) < Real.log 167 * 10 ^ 4 := by
  have hM : ((clbZ 167 : ℕ) : ℝ) = ((5 : ℝ) + 0.1179) * 10 ^ 4 := by
    rw [show clbZ 167 = 51179 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.1179 < Real.log 167 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 167)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1179)
      (by norm_num : (0.1179 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.1179) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.1179 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1179)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.1179) * 10 ^ 4 < Real.log 167 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_173 : ((clbZ 173 : ℕ) : ℝ) < Real.log 173 * 10 ^ 4 := by
  have hM : ((clbZ 173 : ℕ) : ℝ) = ((5 : ℝ) + 0.1532) * 10 ^ 4 := by
    rw [show clbZ 173 = 51532 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.1532 < Real.log 173 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 173)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1532)
      (by norm_num : (0.1532 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.1532) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.1532 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1532)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.1532) * 10 ^ 4 < Real.log 173 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_179 : ((clbZ 179 : ℕ) : ℝ) < Real.log 179 * 10 ^ 4 := by
  have hM : ((clbZ 179 : ℕ) : ℝ) = ((5 : ℝ) + 0.1873) * 10 ^ 4 := by
    rw [show clbZ 179 = 51873 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.1873 < Real.log 179 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 179)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1873)
      (by norm_num : (0.1873 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.1873) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.1873 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1873)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.1873) * 10 ^ 4 < Real.log 179 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_181 : ((clbZ 181 : ℕ) : ℝ) < Real.log 181 * 10 ^ 4 := by
  have hM : ((clbZ 181 : ℕ) : ℝ) = ((5 : ℝ) + 0.1984) * 10 ^ 4 := by
    rw [show clbZ 181 = 51984 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.1984 < Real.log 181 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 181)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1984)
      (by norm_num : (0.1984 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.1984) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.1984 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1984)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.1984) * 10 ^ 4 < Real.log 181 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_191 : ((clbZ 191 : ℕ) : ℝ) < Real.log 191 * 10 ^ 4 := by
  have hM : ((clbZ 191 : ℕ) : ℝ) = ((5 : ℝ) + 0.2522) * 10 ^ 4 := by
    rw [show clbZ 191 = 52522 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.2522 < Real.log 191 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 191)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2522)
      (by norm_num : (0.2522 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.2522) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.2522 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2522)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.2522) * 10 ^ 4 < Real.log 191 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_193 : ((clbZ 193 : ℕ) : ℝ) < Real.log 193 * 10 ^ 4 := by
  have hM : ((clbZ 193 : ℕ) : ℝ) = ((5 : ℝ) + 0.2626) * 10 ^ 4 := by
    rw [show clbZ 193 = 52626 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.2626 < Real.log 193 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 193)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2626)
      (by norm_num : (0.2626 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.2626) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.2626 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2626)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.2626) * 10 ^ 4 < Real.log 193 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_197 : ((clbZ 197 : ℕ) : ℝ) < Real.log 197 * 10 ^ 4 := by
  have hM : ((clbZ 197 : ℕ) : ℝ) = ((5 : ℝ) + 0.2832) * 10 ^ 4 := by
    rw [show clbZ 197 = 52832 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.2832 < Real.log 197 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 197)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2832)
      (by norm_num : (0.2832 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.2832) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.2832 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2832)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.2832) * 10 ^ 4 < Real.log 197 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_199 : ((clbZ 199 : ℕ) : ℝ) < Real.log 199 * 10 ^ 4 := by
  have hM : ((clbZ 199 : ℕ) : ℝ) = ((5 : ℝ) + 0.2933) * 10 ^ 4 := by
    rw [show clbZ 199 = 52933 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.2933 < Real.log 199 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 199)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2933)
      (by norm_num : (0.2933 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.2933) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.2933 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2933)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.2933) * 10 ^ 4 < Real.log 199 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_211 : ((clbZ 211 : ℕ) : ℝ) < Real.log 211 * 10 ^ 4 := by
  have hM : ((clbZ 211 : ℕ) : ℝ) = ((5 : ℝ) + 0.3518) * 10 ^ 4 := by
    rw [show clbZ 211 = 53518 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.3518 < Real.log 211 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 211)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3518)
      (by norm_num : (0.3518 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.3518) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.3518 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3518)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.3518) * 10 ^ 4 < Real.log 211 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_223 : ((clbZ 223 : ℕ) : ℝ) < Real.log 223 * 10 ^ 4 := by
  have hM : ((clbZ 223 : ℕ) : ℝ) = ((5 : ℝ) + 0.4071) * 10 ^ 4 := by
    rw [show clbZ 223 = 54071 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4071 < Real.log 223 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 223)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4071)
      (by norm_num : (0.4071 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4071) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4071 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4071)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4071) * 10 ^ 4 < Real.log 223 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_227 : ((clbZ 227 : ℕ) : ℝ) < Real.log 227 * 10 ^ 4 := by
  have hM : ((clbZ 227 : ℕ) : ℝ) = ((5 : ℝ) + 0.4249) * 10 ^ 4 := by
    rw [show clbZ 227 = 54249 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4249 < Real.log 227 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 227)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4249)
      (by norm_num : (0.4249 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4249) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4249 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4249)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4249) * 10 ^ 4 < Real.log 227 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_229 : ((clbZ 229 : ℕ) : ℝ) < Real.log 229 * 10 ^ 4 := by
  have hM : ((clbZ 229 : ℕ) : ℝ) = ((5 : ℝ) + 0.4337) * 10 ^ 4 := by
    rw [show clbZ 229 = 54337 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4337 < Real.log 229 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 229)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4337)
      (by norm_num : (0.4337 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4337) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4337 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4337)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4337) * 10 ^ 4 < Real.log 229 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_233 : ((clbZ 233 : ℕ) : ℝ) < Real.log 233 * 10 ^ 4 := by
  have hM : ((clbZ 233 : ℕ) : ℝ) = ((5 : ℝ) + 0.4510) * 10 ^ 4 := by
    rw [show clbZ 233 = 54510 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4510 < Real.log 233 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 233)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4510)
      (by norm_num : (0.4510 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4510) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4510 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4510)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4510) * 10 ^ 4 < Real.log 233 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_239 : ((clbZ 239 : ℕ) : ℝ) < Real.log 239 * 10 ^ 4 := by
  have hM : ((clbZ 239 : ℕ) : ℝ) = ((5 : ℝ) + 0.4764) * 10 ^ 4 := by
    rw [show clbZ 239 = 54764 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4764 < Real.log 239 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 239)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4764)
      (by norm_num : (0.4764 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4764) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4764 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4764)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4764) * 10 ^ 4 < Real.log 239 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_241 : ((clbZ 241 : ℕ) : ℝ) < Real.log 241 * 10 ^ 4 := by
  have hM : ((clbZ 241 : ℕ) : ℝ) = ((5 : ℝ) + 0.4847) * 10 ^ 4 := by
    rw [show clbZ 241 = 54847 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.4847 < Real.log 241 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 241)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4847)
      (by norm_num : (0.4847 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.4847) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.4847 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4847)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.4847) * 10 ^ 4 < Real.log 241 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_251 : ((clbZ 251 : ℕ) : ℝ) < Real.log 251 * 10 ^ 4 := by
  have hM : ((clbZ 251 : ℕ) : ℝ) = ((5 : ℝ) + 0.5254) * 10 ^ 4 := by
    rw [show clbZ 251 = 55254 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.5254 < Real.log 251 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 251)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5254)
      (by norm_num : (0.5254 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.5254) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.5254 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5254)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.5254) * 10 ^ 4 < Real.log 251 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_257 : ((clbZ 257 : ℕ) : ℝ) < Real.log 257 * 10 ^ 4 := by
  have hM : ((clbZ 257 : ℕ) : ℝ) = ((5 : ℝ) + 0.5490) * 10 ^ 4 := by
    rw [show clbZ 257 = 55490 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.5490 < Real.log 257 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 257)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5490)
      (by norm_num : (0.5490 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.5490) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.5490 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5490)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.5490) * 10 ^ 4 < Real.log 257 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)


theorem solution (p : ℕ) (hp : p ∈ plist1) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by
  have hmem := hp
  simp only [plist1, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    exact clb_log_2
  · rw [h]
    exact clb_log_3
  · rw [h]
    exact clb_log_5
  · rw [h]
    exact clb_log_7
  · rw [h]
    exact clb_log_11
  · rw [h]
    exact clb_log_13
  · rw [h]
    exact clb_log_17
  · rw [h]
    exact clb_log_19
  · rw [h]
    exact clb_log_23
  · rw [h]
    exact clb_log_29
  · rw [h]
    exact clb_log_31
  · rw [h]
    exact clb_log_37
  · rw [h]
    exact clb_log_41
  · rw [h]
    exact clb_log_43
  · rw [h]
    exact clb_log_47
  · rw [h]
    exact clb_log_53
  · rw [h]
    exact clb_log_59
  · rw [h]
    exact clb_log_61
  · rw [h]
    exact clb_log_67
  · rw [h]
    exact clb_log_71
  · rw [h]
    exact clb_log_73
  · rw [h]
    exact clb_log_79
  · rw [h]
    exact clb_log_83
  · rw [h]
    exact clb_log_89
  · rw [h]
    exact clb_log_97
  · rw [h]
    exact clb_log_101
  · rw [h]
    exact clb_log_103
  · rw [h]
    exact clb_log_107
  · rw [h]
    exact clb_log_109
  · rw [h]
    exact clb_log_113
  · rw [h]
    exact clb_log_127
  · rw [h]
    exact clb_log_131
  · rw [h]
    exact clb_log_137
  · rw [h]
    exact clb_log_139
  · rw [h]
    exact clb_log_149
  · rw [h]
    exact clb_log_151
  · rw [h]
    exact clb_log_157
  · rw [h]
    exact clb_log_163
  · rw [h]
    exact clb_log_167
  · rw [h]
    exact clb_log_173
  · rw [h]
    exact clb_log_179
  · rw [h]
    exact clb_log_181
  · rw [h]
    exact clb_log_191
  · rw [h]
    exact clb_log_193
  · rw [h]
    exact clb_log_197
  · rw [h]
    exact clb_log_199
  · rw [h]
    exact clb_log_211
  · rw [h]
    exact clb_log_223
  · rw [h]
    exact clb_log_227
  · rw [h]
    exact clb_log_229
  · rw [h]
    exact clb_log_233
  · rw [h]
    exact clb_log_239
  · rw [h]
    exact clb_log_241
  · rw [h]
    exact clb_log_251
  · rw [h]
    exact clb_log_257

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (p : ℕ) (hp : p ∈ plist1) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 :=
  TaoFivePrimes.solution p hp
