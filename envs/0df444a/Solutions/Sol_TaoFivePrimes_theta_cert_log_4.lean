-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_log_4
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:33.720113+00:00
-- url     : https://prove2.me/submissions/43277963-28fe-4eda-8118-aa38eb4dcbf4

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

lemma clb_log_983 : ((clbZ 983 : ℕ) : ℝ) < Real.log 983 * 10 ^ 4 := by
  have hM : ((clbZ 983 : ℕ) : ℝ) = ((6 : ℝ) + 0.8906) * 10 ^ 4 := by
    rw [show clbZ 983 = 68906 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8906 < Real.log 983 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 983)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8906)
      (by norm_num : (0.8906 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8906) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8906 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8906)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8906) * 10 ^ 4 < Real.log 983 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_991 : ((clbZ 991 : ℕ) : ℝ) < Real.log 991 * 10 ^ 4 := by
  have hM : ((clbZ 991 : ℕ) : ℝ) = ((6 : ℝ) + 0.8987) * 10 ^ 4 := by
    rw [show clbZ 991 = 68987 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8987 < Real.log 991 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 991)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8987)
      (by norm_num : (0.8987 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8987) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8987 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8987)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8987) * 10 ^ 4 < Real.log 991 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_997 : ((clbZ 997 : ℕ) : ℝ) < Real.log 997 * 10 ^ 4 := by
  have hM : ((clbZ 997 : ℕ) : ℝ) = ((6 : ℝ) + 0.9047) * 10 ^ 4 := by
    rw [show clbZ 997 = 69047 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9047 < Real.log 997 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 997)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9047)
      (by norm_num : (0.9047 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9047) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9047 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9047)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9047) * 10 ^ 4 < Real.log 997 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1009 : ((clbZ 1009 : ℕ) : ℝ) < Real.log 1009 * 10 ^ 4 := by
  have hM : ((clbZ 1009 : ℕ) : ℝ) = ((6 : ℝ) + 0.9167) * 10 ^ 4 := by
    rw [show clbZ 1009 = 69167 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9167 < Real.log 1009 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1009)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9167)
      (by norm_num : (0.9167 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9167) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9167 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9167)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9167) * 10 ^ 4 < Real.log 1009 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1013 : ((clbZ 1013 : ℕ) : ℝ) < Real.log 1013 * 10 ^ 4 := by
  have hM : ((clbZ 1013 : ℕ) : ℝ) = ((6 : ℝ) + 0.9206) * 10 ^ 4 := by
    rw [show clbZ 1013 = 69206 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9206 < Real.log 1013 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1013)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9206)
      (by norm_num : (0.9206 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9206) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9206 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9206)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9206) * 10 ^ 4 < Real.log 1013 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1019 : ((clbZ 1019 : ℕ) : ℝ) < Real.log 1019 * 10 ^ 4 := by
  have hM : ((clbZ 1019 : ℕ) : ℝ) = ((6 : ℝ) + 0.9265) * 10 ^ 4 := by
    rw [show clbZ 1019 = 69265 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9265 < Real.log 1019 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1019)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9265)
      (by norm_num : (0.9265 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9265) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9265 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9265)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9265) * 10 ^ 4 < Real.log 1019 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1021 : ((clbZ 1021 : ℕ) : ℝ) < Real.log 1021 * 10 ^ 4 := by
  have hM : ((clbZ 1021 : ℕ) : ℝ) = ((6 : ℝ) + 0.9285) * 10 ^ 4 := by
    rw [show clbZ 1021 = 69285 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9285 < Real.log 1021 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1021)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9285)
      (by norm_num : (0.9285 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9285) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9285 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9285)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9285) * 10 ^ 4 < Real.log 1021 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1031 : ((clbZ 1031 : ℕ) : ℝ) < Real.log 1031 * 10 ^ 4 := by
  have hM : ((clbZ 1031 : ℕ) : ℝ) = ((6 : ℝ) + 0.9382) * 10 ^ 4 := by
    rw [show clbZ 1031 = 69382 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9382 < Real.log 1031 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1031)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9382)
      (by norm_num : (0.9382 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9382) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9382 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9382)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9382) * 10 ^ 4 < Real.log 1031 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1033 : ((clbZ 1033 : ℕ) : ℝ) < Real.log 1033 * 10 ^ 4 := by
  have hM : ((clbZ 1033 : ℕ) : ℝ) = ((6 : ℝ) + 0.9402) * 10 ^ 4 := by
    rw [show clbZ 1033 = 69402 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9402 < Real.log 1033 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1033)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9402)
      (by norm_num : (0.9402 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9402) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9402 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9402)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9402) * 10 ^ 4 < Real.log 1033 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1039 : ((clbZ 1039 : ℕ) : ℝ) < Real.log 1039 * 10 ^ 4 := by
  have hM : ((clbZ 1039 : ℕ) : ℝ) = ((6 : ℝ) + 0.9460) * 10 ^ 4 := by
    rw [show clbZ 1039 = 69460 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9460 < Real.log 1039 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1039)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9460)
      (by norm_num : (0.9460 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9460) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9460 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9460)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9460) * 10 ^ 4 < Real.log 1039 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1049 : ((clbZ 1049 : ℕ) : ℝ) < Real.log 1049 * 10 ^ 4 := by
  have hM : ((clbZ 1049 : ℕ) : ℝ) = ((6 : ℝ) + 0.9555) * 10 ^ 4 := by
    rw [show clbZ 1049 = 69555 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9555 < Real.log 1049 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1049)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9555)
      (by norm_num : (0.9555 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9555) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9555 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9555)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9555) * 10 ^ 4 < Real.log 1049 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1051 : ((clbZ 1051 : ℕ) : ℝ) < Real.log 1051 * 10 ^ 4 := by
  have hM : ((clbZ 1051 : ℕ) : ℝ) = ((6 : ℝ) + 0.9574) * 10 ^ 4 := by
    rw [show clbZ 1051 = 69574 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9574 < Real.log 1051 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1051)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9574)
      (by norm_num : (0.9574 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9574) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9574 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9574)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9574) * 10 ^ 4 < Real.log 1051 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1061 : ((clbZ 1061 : ℕ) : ℝ) < Real.log 1061 * 10 ^ 4 := by
  have hM : ((clbZ 1061 : ℕ) : ℝ) = ((6 : ℝ) + 0.9669) * 10 ^ 4 := by
    rw [show clbZ 1061 = 69669 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9669 < Real.log 1061 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1061)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9669)
      (by norm_num : (0.9669 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9669) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9669 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9669)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9669) * 10 ^ 4 < Real.log 1061 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1063 : ((clbZ 1063 : ℕ) : ℝ) < Real.log 1063 * 10 ^ 4 := by
  have hM : ((clbZ 1063 : ℕ) : ℝ) = ((6 : ℝ) + 0.9688) * 10 ^ 4 := by
    rw [show clbZ 1063 = 69688 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9688 < Real.log 1063 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1063)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9688)
      (by norm_num : (0.9688 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9688) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9688 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9688)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9688) * 10 ^ 4 < Real.log 1063 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1069 : ((clbZ 1069 : ℕ) : ℝ) < Real.log 1069 * 10 ^ 4 := by
  have hM : ((clbZ 1069 : ℕ) : ℝ) = ((6 : ℝ) + 0.9744) * 10 ^ 4 := by
    rw [show clbZ 1069 = 69744 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9744 < Real.log 1069 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1069)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9744)
      (by norm_num : (0.9744 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9744) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9744 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9744)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9744) * 10 ^ 4 < Real.log 1069 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1087 : ((clbZ 1087 : ℕ) : ℝ) < Real.log 1087 * 10 ^ 4 := by
  have hM : ((clbZ 1087 : ℕ) : ℝ) = ((6 : ℝ) + 0.9911) * 10 ^ 4 := by
    rw [show clbZ 1087 = 69911 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9911 < Real.log 1087 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1087)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9911)
      (by norm_num : (0.9911 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9911) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9911 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9911)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9911) * 10 ^ 4 < Real.log 1087 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1091 : ((clbZ 1091 : ℕ) : ℝ) < Real.log 1091 * 10 ^ 4 := by
  have hM : ((clbZ 1091 : ℕ) : ℝ) = ((6 : ℝ) + 0.9948) * 10 ^ 4 := by
    rw [show clbZ 1091 = 69948 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9948 < Real.log 1091 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1091)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9948)
      (by norm_num : (0.9948 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9948) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9948 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9948)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9948) * 10 ^ 4 < Real.log 1091 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1093 : ((clbZ 1093 : ℕ) : ℝ) < Real.log 1093 * 10 ^ 4 := by
  have hM : ((clbZ 1093 : ℕ) : ℝ) = ((6 : ℝ) + 0.9966) * 10 ^ 4 := by
    rw [show clbZ 1093 = 69966 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.9966 < Real.log 1093 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1093)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.9966)
      (by norm_num : (0.9966 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.9966) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.9966 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.9966)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.9966) * 10 ^ 4 < Real.log 1093 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1097 : ((clbZ 1097 : ℕ) : ℝ) < Real.log 1097 * 10 ^ 4 := by
  have hM : ((clbZ 1097 : ℕ) : ℝ) = ((7 : ℝ) + 0.0003) * 10 ^ 4 := by
    rw [show clbZ 1097 = 70003 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0003 < Real.log 1097 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1097)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0003)
      (by norm_num : (0.0003 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0003) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0003 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0003)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0003) * 10 ^ 4 < Real.log 1097 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1103 : ((clbZ 1103 : ℕ) : ℝ) < Real.log 1103 * 10 ^ 4 := by
  have hM : ((clbZ 1103 : ℕ) : ℝ) = ((7 : ℝ) + 0.0057) * 10 ^ 4 := by
    rw [show clbZ 1103 = 70057 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0057 < Real.log 1103 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1103)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0057)
      (by norm_num : (0.0057 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0057) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0057 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0057)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0057) * 10 ^ 4 < Real.log 1103 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1109 : ((clbZ 1109 : ℕ) : ℝ) < Real.log 1109 * 10 ^ 4 := by
  have hM : ((clbZ 1109 : ℕ) : ℝ) = ((7 : ℝ) + 0.0112) * 10 ^ 4 := by
    rw [show clbZ 1109 = 70112 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0112 < Real.log 1109 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1109)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0112)
      (by norm_num : (0.0112 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0112) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0112 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0112)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0112) * 10 ^ 4 < Real.log 1109 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1117 : ((clbZ 1117 : ℕ) : ℝ) < Real.log 1117 * 10 ^ 4 := by
  have hM : ((clbZ 1117 : ℕ) : ℝ) = ((7 : ℝ) + 0.0184) * 10 ^ 4 := by
    rw [show clbZ 1117 = 70184 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0184 < Real.log 1117 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1117)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0184)
      (by norm_num : (0.0184 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0184) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0184 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0184)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0184) * 10 ^ 4 < Real.log 1117 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1123 : ((clbZ 1123 : ℕ) : ℝ) < Real.log 1123 * 10 ^ 4 := by
  have hM : ((clbZ 1123 : ℕ) : ℝ) = ((7 : ℝ) + 0.0237) * 10 ^ 4 := by
    rw [show clbZ 1123 = 70237 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0237 < Real.log 1123 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1123)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0237)
      (by norm_num : (0.0237 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0237) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0237 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0237)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0237) * 10 ^ 4 < Real.log 1123 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1129 : ((clbZ 1129 : ℕ) : ℝ) < Real.log 1129 * 10 ^ 4 := by
  have hM : ((clbZ 1129 : ℕ) : ℝ) = ((7 : ℝ) + 0.0290) * 10 ^ 4 := by
    rw [show clbZ 1129 = 70290 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0290 < Real.log 1129 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1129)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0290)
      (by norm_num : (0.0290 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0290) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0290 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0290)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0290) * 10 ^ 4 < Real.log 1129 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1151 : ((clbZ 1151 : ℕ) : ℝ) < Real.log 1151 * 10 ^ 4 := by
  have hM : ((clbZ 1151 : ℕ) : ℝ) = ((7 : ℝ) + 0.0483) * 10 ^ 4 := by
    rw [show clbZ 1151 = 70483 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0483 < Real.log 1151 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1151)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0483)
      (by norm_num : (0.0483 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0483) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0483 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0483)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0483) * 10 ^ 4 < Real.log 1151 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1153 : ((clbZ 1153 : ℕ) : ℝ) < Real.log 1153 * 10 ^ 4 := by
  have hM : ((clbZ 1153 : ℕ) : ℝ) = ((7 : ℝ) + 0.0501) * 10 ^ 4 := by
    rw [show clbZ 1153 = 70501 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0501 < Real.log 1153 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1153)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0501)
      (by norm_num : (0.0501 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0501) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0501 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0501)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0501) * 10 ^ 4 < Real.log 1153 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1163 : ((clbZ 1163 : ℕ) : ℝ) < Real.log 1163 * 10 ^ 4 := by
  have hM : ((clbZ 1163 : ℕ) : ℝ) = ((7 : ℝ) + 0.0587) * 10 ^ 4 := by
    rw [show clbZ 1163 = 70587 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0587 < Real.log 1163 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1163)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0587)
      (by norm_num : (0.0587 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0587) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0587 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0587)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0587) * 10 ^ 4 < Real.log 1163 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1171 : ((clbZ 1171 : ℕ) : ℝ) < Real.log 1171 * 10 ^ 4 := by
  have hM : ((clbZ 1171 : ℕ) : ℝ) = ((7 : ℝ) + 0.0656) * 10 ^ 4 := by
    rw [show clbZ 1171 = 70656 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0656 < Real.log 1171 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1171)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0656)
      (by norm_num : (0.0656 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0656) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0656 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0656)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0656) * 10 ^ 4 < Real.log 1171 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1181 : ((clbZ 1181 : ℕ) : ℝ) < Real.log 1181 * 10 ^ 4 := by
  have hM : ((clbZ 1181 : ℕ) : ℝ) = ((7 : ℝ) + 0.0741) * 10 ^ 4 := by
    rw [show clbZ 1181 = 70741 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0741 < Real.log 1181 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1181)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0741)
      (by norm_num : (0.0741 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0741) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0741 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0741)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0741) * 10 ^ 4 < Real.log 1181 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1187 : ((clbZ 1187 : ℕ) : ℝ) < Real.log 1187 * 10 ^ 4 := by
  have hM : ((clbZ 1187 : ℕ) : ℝ) = ((7 : ℝ) + 0.0791) * 10 ^ 4 := by
    rw [show clbZ 1187 = 70791 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0791 < Real.log 1187 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1187)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0791)
      (by norm_num : (0.0791 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0791) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0791 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0791)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0791) * 10 ^ 4 < Real.log 1187 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1193 : ((clbZ 1193 : ℕ) : ℝ) < Real.log 1193 * 10 ^ 4 := by
  have hM : ((clbZ 1193 : ℕ) : ℝ) = ((7 : ℝ) + 0.0842) * 10 ^ 4 := by
    rw [show clbZ 1193 = 70842 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0842 < Real.log 1193 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1193)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0842)
      (by norm_num : (0.0842 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0842) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0842 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0842)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0842) * 10 ^ 4 < Real.log 1193 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1201 : ((clbZ 1201 : ℕ) : ℝ) < Real.log 1201 * 10 ^ 4 := by
  have hM : ((clbZ 1201 : ℕ) : ℝ) = ((7 : ℝ) + 0.0909) * 10 ^ 4 := by
    rw [show clbZ 1201 = 70909 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.0909 < Real.log 1201 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1201)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.0909)
      (by norm_num : (0.0909 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.0909) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.0909 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.0909)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.0909) * 10 ^ 4 < Real.log 1201 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1213 : ((clbZ 1213 : ℕ) : ℝ) < Real.log 1213 * 10 ^ 4 := by
  have hM : ((clbZ 1213 : ℕ) : ℝ) = ((7 : ℝ) + 0.1008) * 10 ^ 4 := by
    rw [show clbZ 1213 = 71008 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1008 < Real.log 1213 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1213)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1008)
      (by norm_num : (0.1008 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1008) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1008 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1008)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1008) * 10 ^ 4 < Real.log 1213 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1217 : ((clbZ 1217 : ℕ) : ℝ) < Real.log 1217 * 10 ^ 4 := by
  have hM : ((clbZ 1217 : ℕ) : ℝ) = ((7 : ℝ) + 0.1041) * 10 ^ 4 := by
    rw [show clbZ 1217 = 71041 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1041 < Real.log 1217 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1217)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1041)
      (by norm_num : (0.1041 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1041) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1041 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1041)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1041) * 10 ^ 4 < Real.log 1217 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1223 : ((clbZ 1223 : ℕ) : ℝ) < Real.log 1223 * 10 ^ 4 := by
  have hM : ((clbZ 1223 : ℕ) : ℝ) = ((7 : ℝ) + 0.1090) * 10 ^ 4 := by
    rw [show clbZ 1223 = 71090 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1090 < Real.log 1223 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1223)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1090)
      (by norm_num : (0.1090 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1090) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1090 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1090)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1090) * 10 ^ 4 < Real.log 1223 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1229 : ((clbZ 1229 : ℕ) : ℝ) < Real.log 1229 * 10 ^ 4 := by
  have hM : ((clbZ 1229 : ℕ) : ℝ) = ((7 : ℝ) + 0.1139) * 10 ^ 4 := by
    rw [show clbZ 1229 = 71139 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1139 < Real.log 1229 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1229)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1139)
      (by norm_num : (0.1139 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1139) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1139 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1139)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1139) * 10 ^ 4 < Real.log 1229 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1231 : ((clbZ 1231 : ℕ) : ℝ) < Real.log 1231 * 10 ^ 4 := by
  have hM : ((clbZ 1231 : ℕ) : ℝ) = ((7 : ℝ) + 0.1155) * 10 ^ 4 := by
    rw [show clbZ 1231 = 71155 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1155 < Real.log 1231 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1231)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1155)
      (by norm_num : (0.1155 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1155) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1155 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1155)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1155) * 10 ^ 4 < Real.log 1231 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1237 : ((clbZ 1237 : ℕ) : ℝ) < Real.log 1237 * 10 ^ 4 := by
  have hM : ((clbZ 1237 : ℕ) : ℝ) = ((7 : ℝ) + 0.1204) * 10 ^ 4 := by
    rw [show clbZ 1237 = 71204 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1204 < Real.log 1237 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1237)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1204)
      (by norm_num : (0.1204 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1204) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1204 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1204)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1204) * 10 ^ 4 < Real.log 1237 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1249 : ((clbZ 1249 : ℕ) : ℝ) < Real.log 1249 * 10 ^ 4 := by
  have hM : ((clbZ 1249 : ℕ) : ℝ) = ((7 : ℝ) + 0.1300) * 10 ^ 4 := by
    rw [show clbZ 1249 = 71300 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1300 < Real.log 1249 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1249)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1300)
      (by norm_num : (0.1300 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1300) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1300 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1300)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1300) * 10 ^ 4 < Real.log 1249 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1259 : ((clbZ 1259 : ℕ) : ℝ) < Real.log 1259 * 10 ^ 4 := by
  have hM : ((clbZ 1259 : ℕ) : ℝ) = ((7 : ℝ) + 0.1380) * 10 ^ 4 := by
    rw [show clbZ 1259 = 71380 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1380 < Real.log 1259 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1259)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1380)
      (by norm_num : (0.1380 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1380) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1380 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1380)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1380) * 10 ^ 4 < Real.log 1259 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1277 : ((clbZ 1277 : ℕ) : ℝ) < Real.log 1277 * 10 ^ 4 := by
  have hM : ((clbZ 1277 : ℕ) : ℝ) = ((7 : ℝ) + 0.1522) * 10 ^ 4 := by
    rw [show clbZ 1277 = 71522 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1522 < Real.log 1277 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1277)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1522)
      (by norm_num : (0.1522 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1522) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1522 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1522)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1522) * 10 ^ 4 < Real.log 1277 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1279 : ((clbZ 1279 : ℕ) : ℝ) < Real.log 1279 * 10 ^ 4 := by
  have hM : ((clbZ 1279 : ℕ) : ℝ) = ((7 : ℝ) + 0.1538) * 10 ^ 4 := by
    rw [show clbZ 1279 = 71538 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1538 < Real.log 1279 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1279)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1538)
      (by norm_num : (0.1538 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1538) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1538 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1538)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1538) * 10 ^ 4 < Real.log 1279 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1283 : ((clbZ 1283 : ℕ) : ℝ) < Real.log 1283 * 10 ^ 4 := by
  have hM : ((clbZ 1283 : ℕ) : ℝ) = ((7 : ℝ) + 0.1569) * 10 ^ 4 := by
    rw [show clbZ 1283 = 71569 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1569 < Real.log 1283 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1283)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1569)
      (by norm_num : (0.1569 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1569) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1569 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1569)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1569) * 10 ^ 4 < Real.log 1283 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1289 : ((clbZ 1289 : ℕ) : ℝ) < Real.log 1289 * 10 ^ 4 := by
  have hM : ((clbZ 1289 : ℕ) : ℝ) = ((7 : ℝ) + 0.1616) * 10 ^ 4 := by
    rw [show clbZ 1289 = 71616 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1616 < Real.log 1289 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1289)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1616)
      (by norm_num : (0.1616 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1616) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1616 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1616)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1616) * 10 ^ 4 < Real.log 1289 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1291 : ((clbZ 1291 : ℕ) : ℝ) < Real.log 1291 * 10 ^ 4 := by
  have hM : ((clbZ 1291 : ℕ) : ℝ) = ((7 : ℝ) + 0.1631) * 10 ^ 4 := by
    rw [show clbZ 1291 = 71631 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1631 < Real.log 1291 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1291)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1631)
      (by norm_num : (0.1631 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1631) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1631 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1631)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1631) * 10 ^ 4 < Real.log 1291 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1297 : ((clbZ 1297 : ℕ) : ℝ) < Real.log 1297 * 10 ^ 4 := by
  have hM : ((clbZ 1297 : ℕ) : ℝ) = ((7 : ℝ) + 0.1678) * 10 ^ 4 := by
    rw [show clbZ 1297 = 71678 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1678 < Real.log 1297 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1297)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1678)
      (by norm_num : (0.1678 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1678) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1678 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1678)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1678) * 10 ^ 4 < Real.log 1297 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1301 : ((clbZ 1301 : ℕ) : ℝ) < Real.log 1301 * 10 ^ 4 := by
  have hM : ((clbZ 1301 : ℕ) : ℝ) = ((7 : ℝ) + 0.1708) * 10 ^ 4 := by
    rw [show clbZ 1301 = 71708 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1708 < Real.log 1301 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1301)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1708)
      (by norm_num : (0.1708 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1708) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1708 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1708)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1708) * 10 ^ 4 < Real.log 1301 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1303 : ((clbZ 1303 : ℕ) : ℝ) < Real.log 1303 * 10 ^ 4 := by
  have hM : ((clbZ 1303 : ℕ) : ℝ) = ((7 : ℝ) + 0.1724) * 10 ^ 4 := by
    rw [show clbZ 1303 = 71724 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1724 < Real.log 1303 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1303)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1724)
      (by norm_num : (0.1724 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1724) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1724 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1724)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1724) * 10 ^ 4 < Real.log 1303 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1307 : ((clbZ 1307 : ℕ) : ℝ) < Real.log 1307 * 10 ^ 4 := by
  have hM : ((clbZ 1307 : ℕ) : ℝ) = ((7 : ℝ) + 0.1754) * 10 ^ 4 := by
    rw [show clbZ 1307 = 71754 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1754 < Real.log 1307 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1307)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1754)
      (by norm_num : (0.1754 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1754) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1754 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1754)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1754) * 10 ^ 4 < Real.log 1307 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1319 : ((clbZ 1319 : ℕ) : ℝ) < Real.log 1319 * 10 ^ 4 := by
  have hM : ((clbZ 1319 : ℕ) : ℝ) = ((7 : ℝ) + 0.1846) * 10 ^ 4 := by
    rw [show clbZ 1319 = 71846 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1846 < Real.log 1319 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1319)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1846)
      (by norm_num : (0.1846 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1846) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1846 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1846)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1846) * 10 ^ 4 < Real.log 1319 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1321 : ((clbZ 1321 : ℕ) : ℝ) < Real.log 1321 * 10 ^ 4 := by
  have hM : ((clbZ 1321 : ℕ) : ℝ) = ((7 : ℝ) + 0.1861) * 10 ^ 4 := by
    rw [show clbZ 1321 = 71861 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1861 < Real.log 1321 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1321)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1861)
      (by norm_num : (0.1861 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1861) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1861 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1861)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1861) * 10 ^ 4 < Real.log 1321 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1327 : ((clbZ 1327 : ℕ) : ℝ) < Real.log 1327 * 10 ^ 4 := by
  have hM : ((clbZ 1327 : ℕ) : ℝ) = ((7 : ℝ) + 0.1906) * 10 ^ 4 := by
    rw [show clbZ 1327 = 71906 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.1906 < Real.log 1327 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1327)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.1906)
      (by norm_num : (0.1906 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.1906) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.1906 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.1906)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.1906) * 10 ^ 4 < Real.log 1327 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1361 : ((clbZ 1361 : ℕ) : ℝ) < Real.log 1361 * 10 ^ 4 := by
  have hM : ((clbZ 1361 : ℕ) : ℝ) = ((7 : ℝ) + 0.2159) * 10 ^ 4 := by
    rw [show clbZ 1361 = 72159 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2159 < Real.log 1361 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1361)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2159)
      (by norm_num : (0.2159 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2159) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2159 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2159)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2159) * 10 ^ 4 < Real.log 1361 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1367 : ((clbZ 1367 : ℕ) : ℝ) < Real.log 1367 * 10 ^ 4 := by
  have hM : ((clbZ 1367 : ℕ) : ℝ) = ((7 : ℝ) + 0.2203) * 10 ^ 4 := by
    rw [show clbZ 1367 = 72203 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2203 < Real.log 1367 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1367)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2203)
      (by norm_num : (0.2203 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2203) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2203 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2203)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2203) * 10 ^ 4 < Real.log 1367 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1373 : ((clbZ 1373 : ℕ) : ℝ) < Real.log 1373 * 10 ^ 4 := by
  have hM : ((clbZ 1373 : ℕ) : ℝ) = ((7 : ℝ) + 0.2247) * 10 ^ 4 := by
    rw [show clbZ 1373 = 72247 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2247 < Real.log 1373 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1373)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2247)
      (by norm_num : (0.2247 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2247) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2247 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2247)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2247) * 10 ^ 4 < Real.log 1373 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1381 : ((clbZ 1381 : ℕ) : ℝ) < Real.log 1381 * 10 ^ 4 := by
  have hM : ((clbZ 1381 : ℕ) : ℝ) = ((7 : ℝ) + 0.2305) * 10 ^ 4 := by
    rw [show clbZ 1381 = 72305 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2305 < Real.log 1381 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1381)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2305)
      (by norm_num : (0.2305 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2305) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2305 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2305)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2305) * 10 ^ 4 < Real.log 1381 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1399 : ((clbZ 1399 : ℕ) : ℝ) < Real.log 1399 * 10 ^ 4 := by
  have hM : ((clbZ 1399 : ℕ) : ℝ) = ((7 : ℝ) + 0.2435) * 10 ^ 4 := by
    rw [show clbZ 1399 = 72435 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2435 < Real.log 1399 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1399)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2435)
      (by norm_num : (0.2435 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2435) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2435 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2435)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2435) * 10 ^ 4 < Real.log 1399 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_1409 : ((clbZ 1409 : ℕ) : ℝ) < Real.log 1409 * 10 ^ 4 := by
  have hM : ((clbZ 1409 : ℕ) : ℝ) = ((7 : ℝ) + 0.2506) * 10 ^ 4 := by
    rw [show clbZ 1409 = 72506 by decide]
    norm_num
  rw [hM]
  have hexp : (7 : ℝ) + 0.2506 < Real.log 1409 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1409)]
    have hm : Real.exp (7 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.2506)
      (by norm_num : (0.2506 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((7 : ℝ) + 0.2506) ≤ (2.7182818286 : ℝ) ^ 7 * Real.exp 0.2506 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.2506)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 7)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((7 : ℝ) + 0.2506) * 10 ^ 4 < Real.log 1409 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)


theorem solution (p : ℕ) (hp : p ∈ plist4) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by
  have hmem := hp
  simp only [plist4, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    exact clb_log_983
  · rw [h]
    exact clb_log_991
  · rw [h]
    exact clb_log_997
  · rw [h]
    exact clb_log_1009
  · rw [h]
    exact clb_log_1013
  · rw [h]
    exact clb_log_1019
  · rw [h]
    exact clb_log_1021
  · rw [h]
    exact clb_log_1031
  · rw [h]
    exact clb_log_1033
  · rw [h]
    exact clb_log_1039
  · rw [h]
    exact clb_log_1049
  · rw [h]
    exact clb_log_1051
  · rw [h]
    exact clb_log_1061
  · rw [h]
    exact clb_log_1063
  · rw [h]
    exact clb_log_1069
  · rw [h]
    exact clb_log_1087
  · rw [h]
    exact clb_log_1091
  · rw [h]
    exact clb_log_1093
  · rw [h]
    exact clb_log_1097
  · rw [h]
    exact clb_log_1103
  · rw [h]
    exact clb_log_1109
  · rw [h]
    exact clb_log_1117
  · rw [h]
    exact clb_log_1123
  · rw [h]
    exact clb_log_1129
  · rw [h]
    exact clb_log_1151
  · rw [h]
    exact clb_log_1153
  · rw [h]
    exact clb_log_1163
  · rw [h]
    exact clb_log_1171
  · rw [h]
    exact clb_log_1181
  · rw [h]
    exact clb_log_1187
  · rw [h]
    exact clb_log_1193
  · rw [h]
    exact clb_log_1201
  · rw [h]
    exact clb_log_1213
  · rw [h]
    exact clb_log_1217
  · rw [h]
    exact clb_log_1223
  · rw [h]
    exact clb_log_1229
  · rw [h]
    exact clb_log_1231
  · rw [h]
    exact clb_log_1237
  · rw [h]
    exact clb_log_1249
  · rw [h]
    exact clb_log_1259
  · rw [h]
    exact clb_log_1277
  · rw [h]
    exact clb_log_1279
  · rw [h]
    exact clb_log_1283
  · rw [h]
    exact clb_log_1289
  · rw [h]
    exact clb_log_1291
  · rw [h]
    exact clb_log_1297
  · rw [h]
    exact clb_log_1301
  · rw [h]
    exact clb_log_1303
  · rw [h]
    exact clb_log_1307
  · rw [h]
    exact clb_log_1319
  · rw [h]
    exact clb_log_1321
  · rw [h]
    exact clb_log_1327
  · rw [h]
    exact clb_log_1361
  · rw [h]
    exact clb_log_1367
  · rw [h]
    exact clb_log_1373
  · rw [h]
    exact clb_log_1381
  · rw [h]
    exact clb_log_1399
  · rw [h]
    exact clb_log_1409

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (p : ℕ) (hp : p ∈ plist4) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 :=
  TaoFivePrimes.solution p hp
