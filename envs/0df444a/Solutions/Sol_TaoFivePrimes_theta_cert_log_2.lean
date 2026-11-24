-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_log_2
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:29.969151+00:00
-- url     : https://prove2.me/submissions/67c0e742-636b-4922-a9f4-24a538aa037e

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

lemma clb_log_263 : ((clbZ 263 : ℕ) : ℝ) < Real.log 263 * 10 ^ 4 := by
  have hM : ((clbZ 263 : ℕ) : ℝ) = ((5 : ℝ) + 0.5721) * 10 ^ 4 := by
    rw [show clbZ 263 = 55721 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.5721 < Real.log 263 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 263)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5721)
      (by norm_num : (0.5721 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.5721) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.5721 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5721)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.5721) * 10 ^ 4 < Real.log 263 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_269 : ((clbZ 269 : ℕ) : ℝ) < Real.log 269 * 10 ^ 4 := by
  have hM : ((clbZ 269 : ℕ) : ℝ) = ((5 : ℝ) + 0.5947) * 10 ^ 4 := by
    rw [show clbZ 269 = 55947 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.5947 < Real.log 269 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 269)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5947)
      (by norm_num : (0.5947 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.5947) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.5947 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5947)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.5947) * 10 ^ 4 < Real.log 269 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_271 : ((clbZ 271 : ℕ) : ℝ) < Real.log 271 * 10 ^ 4 := by
  have hM : ((clbZ 271 : ℕ) : ℝ) = ((5 : ℝ) + 0.6021) * 10 ^ 4 := by
    rw [show clbZ 271 = 56021 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.6021 < Real.log 271 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 271)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6021)
      (by norm_num : (0.6021 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.6021) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.6021 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6021)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.6021) * 10 ^ 4 < Real.log 271 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_277 : ((clbZ 277 : ℕ) : ℝ) < Real.log 277 * 10 ^ 4 := by
  have hM : ((clbZ 277 : ℕ) : ℝ) = ((5 : ℝ) + 0.6240) * 10 ^ 4 := by
    rw [show clbZ 277 = 56240 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.6240 < Real.log 277 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 277)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6240)
      (by norm_num : (0.6240 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.6240) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.6240 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6240)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.6240) * 10 ^ 4 < Real.log 277 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_281 : ((clbZ 281 : ℕ) : ℝ) < Real.log 281 * 10 ^ 4 := by
  have hM : ((clbZ 281 : ℕ) : ℝ) = ((5 : ℝ) + 0.6383) * 10 ^ 4 := by
    rw [show clbZ 281 = 56383 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.6383 < Real.log 281 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 281)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6383)
      (by norm_num : (0.6383 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.6383) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.6383 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6383)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.6383) * 10 ^ 4 < Real.log 281 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_283 : ((clbZ 283 : ℕ) : ℝ) < Real.log 283 * 10 ^ 4 := by
  have hM : ((clbZ 283 : ℕ) : ℝ) = ((5 : ℝ) + 0.6454) * 10 ^ 4 := by
    rw [show clbZ 283 = 56454 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.6454 < Real.log 283 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 283)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6454)
      (by norm_num : (0.6454 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.6454) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.6454 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6454)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.6454) * 10 ^ 4 < Real.log 283 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_293 : ((clbZ 293 : ℕ) : ℝ) < Real.log 293 * 10 ^ 4 := by
  have hM : ((clbZ 293 : ℕ) : ℝ) = ((5 : ℝ) + 0.6801) * 10 ^ 4 := by
    rw [show clbZ 293 = 56801 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.6801 < Real.log 293 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 293)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6801)
      (by norm_num : (0.6801 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.6801) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.6801 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6801)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.6801) * 10 ^ 4 < Real.log 293 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_307 : ((clbZ 307 : ℕ) : ℝ) < Real.log 307 * 10 ^ 4 := by
  have hM : ((clbZ 307 : ℕ) : ℝ) = ((5 : ℝ) + 0.7268) * 10 ^ 4 := by
    rw [show clbZ 307 = 57268 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.7268 < Real.log 307 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 307)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7268)
      (by norm_num : (0.7268 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.7268) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.7268 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7268)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.7268) * 10 ^ 4 < Real.log 307 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_311 : ((clbZ 311 : ℕ) : ℝ) < Real.log 311 * 10 ^ 4 := by
  have hM : ((clbZ 311 : ℕ) : ℝ) = ((5 : ℝ) + 0.7397) * 10 ^ 4 := by
    rw [show clbZ 311 = 57397 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.7397 < Real.log 311 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 311)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7397)
      (by norm_num : (0.7397 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.7397) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.7397 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7397)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.7397) * 10 ^ 4 < Real.log 311 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_313 : ((clbZ 313 : ℕ) : ℝ) < Real.log 313 * 10 ^ 4 := by
  have hM : ((clbZ 313 : ℕ) : ℝ) = ((5 : ℝ) + 0.7462) * 10 ^ 4 := by
    rw [show clbZ 313 = 57462 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.7462 < Real.log 313 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 313)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7462)
      (by norm_num : (0.7462 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.7462) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.7462 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7462)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.7462) * 10 ^ 4 < Real.log 313 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_317 : ((clbZ 317 : ℕ) : ℝ) < Real.log 317 * 10 ^ 4 := by
  have hM : ((clbZ 317 : ℕ) : ℝ) = ((5 : ℝ) + 0.7589) * 10 ^ 4 := by
    rw [show clbZ 317 = 57589 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.7589 < Real.log 317 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 317)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7589)
      (by norm_num : (0.7589 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.7589) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.7589 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7589)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.7589) * 10 ^ 4 < Real.log 317 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_331 : ((clbZ 331 : ℕ) : ℝ) < Real.log 331 * 10 ^ 4 := by
  have hM : ((clbZ 331 : ℕ) : ℝ) = ((5 : ℝ) + 0.8021) * 10 ^ 4 := by
    rw [show clbZ 331 = 58021 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8021 < Real.log 331 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 331)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8021)
      (by norm_num : (0.8021 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8021) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8021 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8021)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8021) * 10 ^ 4 < Real.log 331 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_337 : ((clbZ 337 : ℕ) : ℝ) < Real.log 337 * 10 ^ 4 := by
  have hM : ((clbZ 337 : ℕ) : ℝ) = ((5 : ℝ) + 0.8200) * 10 ^ 4 := by
    rw [show clbZ 337 = 58200 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8200 < Real.log 337 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 337)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8200)
      (by norm_num : (0.8200 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8200) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8200 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8200)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8200) * 10 ^ 4 < Real.log 337 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_347 : ((clbZ 347 : ℕ) : ℝ) < Real.log 347 * 10 ^ 4 := by
  have hM : ((clbZ 347 : ℕ) : ℝ) = ((5 : ℝ) + 0.8493) * 10 ^ 4 := by
    rw [show clbZ 347 = 58493 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8493 < Real.log 347 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 347)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8493)
      (by norm_num : (0.8493 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8493) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8493 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8493)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8493) * 10 ^ 4 < Real.log 347 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_349 : ((clbZ 349 : ℕ) : ℝ) < Real.log 349 * 10 ^ 4 := by
  have hM : ((clbZ 349 : ℕ) : ℝ) = ((5 : ℝ) + 0.8550) * 10 ^ 4 := by
    rw [show clbZ 349 = 58550 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8550 < Real.log 349 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 349)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8550)
      (by norm_num : (0.8550 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8550) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8550 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8550)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8550) * 10 ^ 4 < Real.log 349 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_353 : ((clbZ 353 : ℕ) : ℝ) < Real.log 353 * 10 ^ 4 := by
  have hM : ((clbZ 353 : ℕ) : ℝ) = ((5 : ℝ) + 0.8664) * 10 ^ 4 := by
    rw [show clbZ 353 = 58664 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8664 < Real.log 353 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 353)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8664)
      (by norm_num : (0.8664 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8664) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8664 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8664)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8664) * 10 ^ 4 < Real.log 353 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_359 : ((clbZ 359 : ℕ) : ℝ) < Real.log 359 * 10 ^ 4 := by
  have hM : ((clbZ 359 : ℕ) : ℝ) = ((5 : ℝ) + 0.8833) * 10 ^ 4 := by
    rw [show clbZ 359 = 58833 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.8833 < Real.log 359 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 359)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8833)
      (by norm_num : (0.8833 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.8833) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.8833 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8833)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.8833) * 10 ^ 4 < Real.log 359 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_367 : ((clbZ 367 : ℕ) : ℝ) < Real.log 367 * 10 ^ 4 := by
  have hM : ((clbZ 367 : ℕ) : ℝ) = ((5 : ℝ) + 0.9053) * 10 ^ 4 := by
    rw [show clbZ 367 = 59053 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9053 < Real.log 367 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 367)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9053)
      (by norm_num : (0.9053 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9053) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9053 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9053)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9053) * 10 ^ 4 < Real.log 367 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_373 : ((clbZ 373 : ℕ) : ℝ) < Real.log 373 * 10 ^ 4 := by
  have hM : ((clbZ 373 : ℕ) : ℝ) = ((5 : ℝ) + 0.9215) * 10 ^ 4 := by
    rw [show clbZ 373 = 59215 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9215 < Real.log 373 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 373)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9215)
      (by norm_num : (0.9215 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9215) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9215 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9215)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9215) * 10 ^ 4 < Real.log 373 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_379 : ((clbZ 379 : ℕ) : ℝ) < Real.log 379 * 10 ^ 4 := by
  have hM : ((clbZ 379 : ℕ) : ℝ) = ((5 : ℝ) + 0.9375) * 10 ^ 4 := by
    rw [show clbZ 379 = 59375 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9375 < Real.log 379 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 379)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9375)
      (by norm_num : (0.9375 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9375) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9375 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9375)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9375) * 10 ^ 4 < Real.log 379 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_383 : ((clbZ 383 : ℕ) : ℝ) < Real.log 383 * 10 ^ 4 := by
  have hM : ((clbZ 383 : ℕ) : ℝ) = ((5 : ℝ) + 0.9480) * 10 ^ 4 := by
    rw [show clbZ 383 = 59480 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9480 < Real.log 383 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 383)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9480)
      (by norm_num : (0.9480 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9480) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9480 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9480)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9480) * 10 ^ 4 < Real.log 383 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_389 : ((clbZ 389 : ℕ) : ℝ) < Real.log 389 * 10 ^ 4 := by
  have hM : ((clbZ 389 : ℕ) : ℝ) = ((5 : ℝ) + 0.9635) * 10 ^ 4 := by
    rw [show clbZ 389 = 59635 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9635 < Real.log 389 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 389)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9635)
      (by norm_num : (0.9635 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9635) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9635 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9635)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9635) * 10 ^ 4 < Real.log 389 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_397 : ((clbZ 397 : ℕ) : ℝ) < Real.log 397 * 10 ^ 4 := by
  have hM : ((clbZ 397 : ℕ) : ℝ) = ((5 : ℝ) + 0.9839) * 10 ^ 4 := by
    rw [show clbZ 397 = 59839 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9839 < Real.log 397 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 397)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9839)
      (by norm_num : (0.9839 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9839) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9839 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9839)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9839) * 10 ^ 4 < Real.log 397 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_401 : ((clbZ 401 : ℕ) : ℝ) < Real.log 401 * 10 ^ 4 := by
  have hM : ((clbZ 401 : ℕ) : ℝ) = ((5 : ℝ) + 0.9939) * 10 ^ 4 := by
    rw [show clbZ 401 = 59939 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.9939 < Real.log 401 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 401)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9939)
      (by norm_num : (0.9939 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.9939) ≤ (2.7182818286 : ℝ) ^ 5 * Real.exp 0.9939 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9939)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.9939) * 10 ^ 4 < Real.log 401 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_409 : ((clbZ 409 : ℕ) : ℝ) < Real.log 409 * 10 ^ 4 := by
  have hM : ((clbZ 409 : ℕ) : ℝ) = ((6 : ℝ) + 0.0137) * 10 ^ 4 := by
    rw [show clbZ 409 = 60137 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0137 < Real.log 409 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 409)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0137)
      (by norm_num : (0.0137 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0137) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0137 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0137)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0137) * 10 ^ 4 < Real.log 409 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_419 : ((clbZ 419 : ℕ) : ℝ) < Real.log 419 * 10 ^ 4 := by
  have hM : ((clbZ 419 : ℕ) : ℝ) = ((6 : ℝ) + 0.0378) * 10 ^ 4 := by
    rw [show clbZ 419 = 60378 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0378 < Real.log 419 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 419)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0378)
      (by norm_num : (0.0378 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0378) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0378 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0378)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0378) * 10 ^ 4 < Real.log 419 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_421 : ((clbZ 421 : ℕ) : ℝ) < Real.log 421 * 10 ^ 4 := by
  have hM : ((clbZ 421 : ℕ) : ℝ) = ((6 : ℝ) + 0.0426) * 10 ^ 4 := by
    rw [show clbZ 421 = 60426 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0426 < Real.log 421 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 421)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0426)
      (by norm_num : (0.0426 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0426) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0426 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0426)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0426) * 10 ^ 4 < Real.log 421 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_431 : ((clbZ 431 : ℕ) : ℝ) < Real.log 431 * 10 ^ 4 := by
  have hM : ((clbZ 431 : ℕ) : ℝ) = ((6 : ℝ) + 0.0661) * 10 ^ 4 := by
    rw [show clbZ 431 = 60661 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0661 < Real.log 431 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 431)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0661)
      (by norm_num : (0.0661 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0661) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0661 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0661)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0661) * 10 ^ 4 < Real.log 431 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_433 : ((clbZ 433 : ℕ) : ℝ) < Real.log 433 * 10 ^ 4 := by
  have hM : ((clbZ 433 : ℕ) : ℝ) = ((6 : ℝ) + 0.0707) * 10 ^ 4 := by
    rw [show clbZ 433 = 60707 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0707 < Real.log 433 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 433)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0707)
      (by norm_num : (0.0707 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0707) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0707 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0707)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0707) * 10 ^ 4 < Real.log 433 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_439 : ((clbZ 439 : ℕ) : ℝ) < Real.log 439 * 10 ^ 4 := by
  have hM : ((clbZ 439 : ℕ) : ℝ) = ((6 : ℝ) + 0.0844) * 10 ^ 4 := by
    rw [show clbZ 439 = 60844 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0844 < Real.log 439 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 439)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0844)
      (by norm_num : (0.0844 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0844) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0844 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0844)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0844) * 10 ^ 4 < Real.log 439 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_443 : ((clbZ 443 : ℕ) : ℝ) < Real.log 443 * 10 ^ 4 := by
  have hM : ((clbZ 443 : ℕ) : ℝ) = ((6 : ℝ) + 0.0935) * 10 ^ 4 := by
    rw [show clbZ 443 = 60935 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.0935 < Real.log 443 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 443)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0935)
      (by norm_num : (0.0935 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.0935) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.0935 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0935)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.0935) * 10 ^ 4 < Real.log 443 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_449 : ((clbZ 449 : ℕ) : ℝ) < Real.log 449 * 10 ^ 4 := by
  have hM : ((clbZ 449 : ℕ) : ℝ) = ((6 : ℝ) + 0.1070) * 10 ^ 4 := by
    rw [show clbZ 449 = 61070 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1070 < Real.log 449 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 449)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1070)
      (by norm_num : (0.1070 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1070) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1070 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1070)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1070) * 10 ^ 4 < Real.log 449 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_457 : ((clbZ 457 : ℕ) : ℝ) < Real.log 457 * 10 ^ 4 := by
  have hM : ((clbZ 457 : ℕ) : ℝ) = ((6 : ℝ) + 0.1246) * 10 ^ 4 := by
    rw [show clbZ 457 = 61246 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1246 < Real.log 457 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 457)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1246)
      (by norm_num : (0.1246 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1246) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1246 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1246)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1246) * 10 ^ 4 < Real.log 457 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_461 : ((clbZ 461 : ℕ) : ℝ) < Real.log 461 * 10 ^ 4 := by
  have hM : ((clbZ 461 : ℕ) : ℝ) = ((6 : ℝ) + 0.1333) * 10 ^ 4 := by
    rw [show clbZ 461 = 61333 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1333 < Real.log 461 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 461)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1333)
      (by norm_num : (0.1333 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1333) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1333 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1333)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1333) * 10 ^ 4 < Real.log 461 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_463 : ((clbZ 463 : ℕ) : ℝ) < Real.log 463 * 10 ^ 4 := by
  have hM : ((clbZ 463 : ℕ) : ℝ) = ((6 : ℝ) + 0.1377) * 10 ^ 4 := by
    rw [show clbZ 463 = 61377 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1377 < Real.log 463 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 463)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1377)
      (by norm_num : (0.1377 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1377) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1377 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1377)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1377) * 10 ^ 4 < Real.log 463 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_467 : ((clbZ 467 : ℕ) : ℝ) < Real.log 467 * 10 ^ 4 := by
  have hM : ((clbZ 467 : ℕ) : ℝ) = ((6 : ℝ) + 0.1463) * 10 ^ 4 := by
    rw [show clbZ 467 = 61463 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1463 < Real.log 467 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 467)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1463)
      (by norm_num : (0.1463 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1463) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1463 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1463)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1463) * 10 ^ 4 < Real.log 467 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_479 : ((clbZ 479 : ℕ) : ℝ) < Real.log 479 * 10 ^ 4 := by
  have hM : ((clbZ 479 : ℕ) : ℝ) = ((6 : ℝ) + 0.1717) * 10 ^ 4 := by
    rw [show clbZ 479 = 61717 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1717 < Real.log 479 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 479)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1717)
      (by norm_num : (0.1717 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1717) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1717 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1717)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1717) * 10 ^ 4 < Real.log 479 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_487 : ((clbZ 487 : ℕ) : ℝ) < Real.log 487 * 10 ^ 4 := by
  have hM : ((clbZ 487 : ℕ) : ℝ) = ((6 : ℝ) + 0.1882) * 10 ^ 4 := by
    rw [show clbZ 487 = 61882 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1882 < Real.log 487 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 487)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1882)
      (by norm_num : (0.1882 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1882) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1882 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1882)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1882) * 10 ^ 4 < Real.log 487 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_491 : ((clbZ 491 : ℕ) : ℝ) < Real.log 491 * 10 ^ 4 := by
  have hM : ((clbZ 491 : ℕ) : ℝ) = ((6 : ℝ) + 0.1964) * 10 ^ 4 := by
    rw [show clbZ 491 = 61964 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.1964 < Real.log 491 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 491)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1964)
      (by norm_num : (0.1964 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.1964) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.1964 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1964)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.1964) * 10 ^ 4 < Real.log 491 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_499 : ((clbZ 499 : ℕ) : ℝ) < Real.log 499 * 10 ^ 4 := by
  have hM : ((clbZ 499 : ℕ) : ℝ) = ((6 : ℝ) + 0.2126) * 10 ^ 4 := by
    rw [show clbZ 499 = 62126 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2126 < Real.log 499 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 499)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2126)
      (by norm_num : (0.2126 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2126) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2126 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2126)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2126) * 10 ^ 4 < Real.log 499 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_503 : ((clbZ 503 : ℕ) : ℝ) < Real.log 503 * 10 ^ 4 := by
  have hM : ((clbZ 503 : ℕ) : ℝ) = ((6 : ℝ) + 0.2205) * 10 ^ 4 := by
    rw [show clbZ 503 = 62205 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2205 < Real.log 503 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 503)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2205)
      (by norm_num : (0.2205 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2205) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2205 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2205)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2205) * 10 ^ 4 < Real.log 503 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_509 : ((clbZ 509 : ℕ) : ℝ) < Real.log 509 * 10 ^ 4 := by
  have hM : ((clbZ 509 : ℕ) : ℝ) = ((6 : ℝ) + 0.2324) * 10 ^ 4 := by
    rw [show clbZ 509 = 62324 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2324 < Real.log 509 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 509)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2324)
      (by norm_num : (0.2324 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2324) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2324 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2324)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2324) * 10 ^ 4 < Real.log 509 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_521 : ((clbZ 521 : ℕ) : ℝ) < Real.log 521 * 10 ^ 4 := by
  have hM : ((clbZ 521 : ℕ) : ℝ) = ((6 : ℝ) + 0.2557) * 10 ^ 4 := by
    rw [show clbZ 521 = 62557 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2557 < Real.log 521 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 521)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2557)
      (by norm_num : (0.2557 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2557) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2557 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2557)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2557) * 10 ^ 4 < Real.log 521 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_523 : ((clbZ 523 : ℕ) : ℝ) < Real.log 523 * 10 ^ 4 := by
  have hM : ((clbZ 523 : ℕ) : ℝ) = ((6 : ℝ) + 0.2595) * 10 ^ 4 := by
    rw [show clbZ 523 = 62595 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2595 < Real.log 523 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 523)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2595)
      (by norm_num : (0.2595 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2595) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2595 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2595)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2595) * 10 ^ 4 < Real.log 523 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_541 : ((clbZ 541 : ℕ) : ℝ) < Real.log 541 * 10 ^ 4 := by
  have hM : ((clbZ 541 : ℕ) : ℝ) = ((6 : ℝ) + 0.2934) * 10 ^ 4 := by
    rw [show clbZ 541 = 62934 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.2934 < Real.log 541 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 541)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2934)
      (by norm_num : (0.2934 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.2934) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.2934 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2934)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.2934) * 10 ^ 4 < Real.log 541 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_547 : ((clbZ 547 : ℕ) : ℝ) < Real.log 547 * 10 ^ 4 := by
  have hM : ((clbZ 547 : ℕ) : ℝ) = ((6 : ℝ) + 0.3044) * 10 ^ 4 := by
    rw [show clbZ 547 = 63044 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3044 < Real.log 547 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 547)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3044)
      (by norm_num : (0.3044 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3044) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3044 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3044)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3044) * 10 ^ 4 < Real.log 547 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_557 : ((clbZ 557 : ℕ) : ℝ) < Real.log 557 * 10 ^ 4 := by
  have hM : ((clbZ 557 : ℕ) : ℝ) = ((6 : ℝ) + 0.3225) * 10 ^ 4 := by
    rw [show clbZ 557 = 63225 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3225 < Real.log 557 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 557)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3225)
      (by norm_num : (0.3225 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3225) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3225 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3225)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3225) * 10 ^ 4 < Real.log 557 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_563 : ((clbZ 563 : ℕ) : ℝ) < Real.log 563 * 10 ^ 4 := by
  have hM : ((clbZ 563 : ℕ) : ℝ) = ((6 : ℝ) + 0.3332) * 10 ^ 4 := by
    rw [show clbZ 563 = 63332 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3332 < Real.log 563 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 563)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3332)
      (by norm_num : (0.3332 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3332) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3332 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3332)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3332) * 10 ^ 4 < Real.log 563 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_569 : ((clbZ 569 : ℕ) : ℝ) < Real.log 569 * 10 ^ 4 := by
  have hM : ((clbZ 569 : ℕ) : ℝ) = ((6 : ℝ) + 0.3438) * 10 ^ 4 := by
    rw [show clbZ 569 = 63438 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3438 < Real.log 569 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 569)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3438)
      (by norm_num : (0.3438 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3438) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3438 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3438)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3438) * 10 ^ 4 < Real.log 569 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_571 : ((clbZ 571 : ℕ) : ℝ) < Real.log 571 * 10 ^ 4 := by
  have hM : ((clbZ 571 : ℕ) : ℝ) = ((6 : ℝ) + 0.3473) * 10 ^ 4 := by
    rw [show clbZ 571 = 63473 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3473 < Real.log 571 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 571)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3473)
      (by norm_num : (0.3473 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3473) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3473 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3473)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3473) * 10 ^ 4 < Real.log 571 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_577 : ((clbZ 577 : ℕ) : ℝ) < Real.log 577 * 10 ^ 4 := by
  have hM : ((clbZ 577 : ℕ) : ℝ) = ((6 : ℝ) + 0.3578) * 10 ^ 4 := by
    rw [show clbZ 577 = 63578 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3578 < Real.log 577 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 577)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3578)
      (by norm_num : (0.3578 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3578) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3578 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3578)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3578) * 10 ^ 4 < Real.log 577 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_587 : ((clbZ 587 : ℕ) : ℝ) < Real.log 587 * 10 ^ 4 := by
  have hM : ((clbZ 587 : ℕ) : ℝ) = ((6 : ℝ) + 0.3750) * 10 ^ 4 := by
    rw [show clbZ 587 = 63750 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3750 < Real.log 587 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 587)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3750)
      (by norm_num : (0.3750 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3750) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3750 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3750)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3750) * 10 ^ 4 < Real.log 587 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_593 : ((clbZ 593 : ℕ) : ℝ) < Real.log 593 * 10 ^ 4 := by
  have hM : ((clbZ 593 : ℕ) : ℝ) = ((6 : ℝ) + 0.3851) * 10 ^ 4 := by
    rw [show clbZ 593 = 63851 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3851 < Real.log 593 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 593)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3851)
      (by norm_num : (0.3851 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3851) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3851 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3851)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3851) * 10 ^ 4 < Real.log 593 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_599 : ((clbZ 599 : ℕ) : ℝ) < Real.log 599 * 10 ^ 4 := by
  have hM : ((clbZ 599 : ℕ) : ℝ) = ((6 : ℝ) + 0.3952) * 10 ^ 4 := by
    rw [show clbZ 599 = 63952 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3952 < Real.log 599 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 599)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3952)
      (by norm_num : (0.3952 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3952) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3952 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3952)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3952) * 10 ^ 4 < Real.log 599 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_601 : ((clbZ 601 : ℕ) : ℝ) < Real.log 601 * 10 ^ 4 := by
  have hM : ((clbZ 601 : ℕ) : ℝ) = ((6 : ℝ) + 0.3985) * 10 ^ 4 := by
    rw [show clbZ 601 = 63985 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.3985 < Real.log 601 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 601)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3985)
      (by norm_num : (0.3985 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.3985) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.3985 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.3985)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.3985) * 10 ^ 4 < Real.log 601 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)


theorem solution (p : ℕ) (hp : p ∈ plist2) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by
  have hmem := hp
  simp only [plist2, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    exact clb_log_263
  · rw [h]
    exact clb_log_269
  · rw [h]
    exact clb_log_271
  · rw [h]
    exact clb_log_277
  · rw [h]
    exact clb_log_281
  · rw [h]
    exact clb_log_283
  · rw [h]
    exact clb_log_293
  · rw [h]
    exact clb_log_307
  · rw [h]
    exact clb_log_311
  · rw [h]
    exact clb_log_313
  · rw [h]
    exact clb_log_317
  · rw [h]
    exact clb_log_331
  · rw [h]
    exact clb_log_337
  · rw [h]
    exact clb_log_347
  · rw [h]
    exact clb_log_349
  · rw [h]
    exact clb_log_353
  · rw [h]
    exact clb_log_359
  · rw [h]
    exact clb_log_367
  · rw [h]
    exact clb_log_373
  · rw [h]
    exact clb_log_379
  · rw [h]
    exact clb_log_383
  · rw [h]
    exact clb_log_389
  · rw [h]
    exact clb_log_397
  · rw [h]
    exact clb_log_401
  · rw [h]
    exact clb_log_409
  · rw [h]
    exact clb_log_419
  · rw [h]
    exact clb_log_421
  · rw [h]
    exact clb_log_431
  · rw [h]
    exact clb_log_433
  · rw [h]
    exact clb_log_439
  · rw [h]
    exact clb_log_443
  · rw [h]
    exact clb_log_449
  · rw [h]
    exact clb_log_457
  · rw [h]
    exact clb_log_461
  · rw [h]
    exact clb_log_463
  · rw [h]
    exact clb_log_467
  · rw [h]
    exact clb_log_479
  · rw [h]
    exact clb_log_487
  · rw [h]
    exact clb_log_491
  · rw [h]
    exact clb_log_499
  · rw [h]
    exact clb_log_503
  · rw [h]
    exact clb_log_509
  · rw [h]
    exact clb_log_521
  · rw [h]
    exact clb_log_523
  · rw [h]
    exact clb_log_541
  · rw [h]
    exact clb_log_547
  · rw [h]
    exact clb_log_557
  · rw [h]
    exact clb_log_563
  · rw [h]
    exact clb_log_569
  · rw [h]
    exact clb_log_571
  · rw [h]
    exact clb_log_577
  · rw [h]
    exact clb_log_587
  · rw [h]
    exact clb_log_593
  · rw [h]
    exact clb_log_599
  · rw [h]
    exact clb_log_601

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (p : ℕ) (hp : p ∈ plist2) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 :=
  TaoFivePrimes.solution p hp
