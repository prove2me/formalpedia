-- Prove2me | solution 1 for TaoFivePrimes.theta_cert_log_3
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T13:49:31.956015+00:00
-- url     : https://prove2.me/submissions/107222d5-c12b-42f6-8c86-f1557681037a

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

lemma clb_log_607 : ((clbZ 607 : ℕ) : ℝ) < Real.log 607 * 10 ^ 4 := by
  have hM : ((clbZ 607 : ℕ) : ℝ) = ((6 : ℝ) + 0.4085) * 10 ^ 4 := by
    rw [show clbZ 607 = 64085 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4085 < Real.log 607 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 607)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4085)
      (by norm_num : (0.4085 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4085) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4085 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4085)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4085) * 10 ^ 4 < Real.log 607 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_613 : ((clbZ 613 : ℕ) : ℝ) < Real.log 613 * 10 ^ 4 := by
  have hM : ((clbZ 613 : ℕ) : ℝ) = ((6 : ℝ) + 0.4183) * 10 ^ 4 := by
    rw [show clbZ 613 = 64183 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4183 < Real.log 613 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 613)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4183)
      (by norm_num : (0.4183 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4183) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4183 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4183)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4183) * 10 ^ 4 < Real.log 613 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_617 : ((clbZ 617 : ℕ) : ℝ) < Real.log 617 * 10 ^ 4 := by
  have hM : ((clbZ 617 : ℕ) : ℝ) = ((6 : ℝ) + 0.4248) * 10 ^ 4 := by
    rw [show clbZ 617 = 64248 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4248 < Real.log 617 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 617)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4248)
      (by norm_num : (0.4248 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4248) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4248 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4248)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4248) * 10 ^ 4 < Real.log 617 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_619 : ((clbZ 619 : ℕ) : ℝ) < Real.log 619 * 10 ^ 4 := by
  have hM : ((clbZ 619 : ℕ) : ℝ) = ((6 : ℝ) + 0.4281) * 10 ^ 4 := by
    rw [show clbZ 619 = 64281 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4281 < Real.log 619 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 619)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4281)
      (by norm_num : (0.4281 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4281) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4281 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4281)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4281) * 10 ^ 4 < Real.log 619 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_631 : ((clbZ 631 : ℕ) : ℝ) < Real.log 631 * 10 ^ 4 := by
  have hM : ((clbZ 631 : ℕ) : ℝ) = ((6 : ℝ) + 0.4473) * 10 ^ 4 := by
    rw [show clbZ 631 = 64473 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4473 < Real.log 631 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 631)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4473)
      (by norm_num : (0.4473 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4473) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4473 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4473)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4473) * 10 ^ 4 < Real.log 631 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_641 : ((clbZ 641 : ℕ) : ℝ) < Real.log 641 * 10 ^ 4 := by
  have hM : ((clbZ 641 : ℕ) : ℝ) = ((6 : ℝ) + 0.4630) * 10 ^ 4 := by
    rw [show clbZ 641 = 64630 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4630 < Real.log 641 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 641)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4630)
      (by norm_num : (0.4630 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4630) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4630 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4630)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4630) * 10 ^ 4 < Real.log 641 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_643 : ((clbZ 643 : ℕ) : ℝ) < Real.log 643 * 10 ^ 4 := by
  have hM : ((clbZ 643 : ℕ) : ℝ) = ((6 : ℝ) + 0.4661) * 10 ^ 4 := by
    rw [show clbZ 643 = 64661 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4661 < Real.log 643 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 643)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4661)
      (by norm_num : (0.4661 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4661) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4661 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4661)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4661) * 10 ^ 4 < Real.log 643 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_647 : ((clbZ 647 : ℕ) : ℝ) < Real.log 647 * 10 ^ 4 := by
  have hM : ((clbZ 647 : ℕ) : ℝ) = ((6 : ℝ) + 0.4723) * 10 ^ 4 := by
    rw [show clbZ 647 = 64723 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4723 < Real.log 647 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 647)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4723)
      (by norm_num : (0.4723 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4723) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4723 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4723)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4723) * 10 ^ 4 < Real.log 647 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_653 : ((clbZ 653 : ℕ) : ℝ) < Real.log 653 * 10 ^ 4 := by
  have hM : ((clbZ 653 : ℕ) : ℝ) = ((6 : ℝ) + 0.4815) * 10 ^ 4 := by
    rw [show clbZ 653 = 64815 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4815 < Real.log 653 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 653)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4815)
      (by norm_num : (0.4815 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4815) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4815 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4815)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4815) * 10 ^ 4 < Real.log 653 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_659 : ((clbZ 659 : ℕ) : ℝ) < Real.log 659 * 10 ^ 4 := by
  have hM : ((clbZ 659 : ℕ) : ℝ) = ((6 : ℝ) + 0.4907) * 10 ^ 4 := by
    rw [show clbZ 659 = 64907 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4907 < Real.log 659 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 659)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4907)
      (by norm_num : (0.4907 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4907) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4907 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4907)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4907) * 10 ^ 4 < Real.log 659 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_661 : ((clbZ 661 : ℕ) : ℝ) < Real.log 661 * 10 ^ 4 := by
  have hM : ((clbZ 661 : ℕ) : ℝ) = ((6 : ℝ) + 0.4937) * 10 ^ 4 := by
    rw [show clbZ 661 = 64937 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.4937 < Real.log 661 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 661)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.4937)
      (by norm_num : (0.4937 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.4937) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.4937 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.4937)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.4937) * 10 ^ 4 < Real.log 661 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_673 : ((clbZ 673 : ℕ) : ℝ) < Real.log 673 * 10 ^ 4 := by
  have hM : ((clbZ 673 : ℕ) : ℝ) = ((6 : ℝ) + 0.5117) * 10 ^ 4 := by
    rw [show clbZ 673 = 65117 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5117 < Real.log 673 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 673)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5117)
      (by norm_num : (0.5117 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5117) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5117 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5117)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5117) * 10 ^ 4 < Real.log 673 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_677 : ((clbZ 677 : ℕ) : ℝ) < Real.log 677 * 10 ^ 4 := by
  have hM : ((clbZ 677 : ℕ) : ℝ) = ((6 : ℝ) + 0.5176) * 10 ^ 4 := by
    rw [show clbZ 677 = 65176 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5176 < Real.log 677 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 677)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5176)
      (by norm_num : (0.5176 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5176) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5176 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5176)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5176) * 10 ^ 4 < Real.log 677 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_683 : ((clbZ 683 : ℕ) : ℝ) < Real.log 683 * 10 ^ 4 := by
  have hM : ((clbZ 683 : ℕ) : ℝ) = ((6 : ℝ) + 0.5264) * 10 ^ 4 := by
    rw [show clbZ 683 = 65264 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5264 < Real.log 683 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 683)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5264)
      (by norm_num : (0.5264 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5264) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5264 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5264)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5264) * 10 ^ 4 < Real.log 683 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_691 : ((clbZ 691 : ℕ) : ℝ) < Real.log 691 * 10 ^ 4 := by
  have hM : ((clbZ 691 : ℕ) : ℝ) = ((6 : ℝ) + 0.5381) * 10 ^ 4 := by
    rw [show clbZ 691 = 65381 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5381 < Real.log 691 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 691)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5381)
      (by norm_num : (0.5381 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5381) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5381 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5381)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5381) * 10 ^ 4 < Real.log 691 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_701 : ((clbZ 701 : ℕ) : ℝ) < Real.log 701 * 10 ^ 4 := by
  have hM : ((clbZ 701 : ℕ) : ℝ) = ((6 : ℝ) + 0.5525) * 10 ^ 4 := by
    rw [show clbZ 701 = 65525 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5525 < Real.log 701 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 701)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5525)
      (by norm_num : (0.5525 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5525) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5525 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5525)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5525) * 10 ^ 4 < Real.log 701 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_709 : ((clbZ 709 : ℕ) : ℝ) < Real.log 709 * 10 ^ 4 := by
  have hM : ((clbZ 709 : ℕ) : ℝ) = ((6 : ℝ) + 0.5638) * 10 ^ 4 := by
    rw [show clbZ 709 = 65638 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5638 < Real.log 709 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 709)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5638)
      (by norm_num : (0.5638 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5638) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5638 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5638)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5638) * 10 ^ 4 < Real.log 709 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_719 : ((clbZ 719 : ℕ) : ℝ) < Real.log 719 * 10 ^ 4 := by
  have hM : ((clbZ 719 : ℕ) : ℝ) = ((6 : ℝ) + 0.5778) * 10 ^ 4 := by
    rw [show clbZ 719 = 65778 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5778 < Real.log 719 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 719)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5778)
      (by norm_num : (0.5778 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5778) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5778 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5778)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5778) * 10 ^ 4 < Real.log 719 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_727 : ((clbZ 727 : ℕ) : ℝ) < Real.log 727 * 10 ^ 4 := by
  have hM : ((clbZ 727 : ℕ) : ℝ) = ((6 : ℝ) + 0.5889) * 10 ^ 4 := by
    rw [show clbZ 727 = 65889 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5889 < Real.log 727 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 727)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5889)
      (by norm_num : (0.5889 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5889) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5889 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5889)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5889) * 10 ^ 4 < Real.log 727 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_733 : ((clbZ 733 : ℕ) : ℝ) < Real.log 733 * 10 ^ 4 := by
  have hM : ((clbZ 733 : ℕ) : ℝ) = ((6 : ℝ) + 0.5971) * 10 ^ 4 := by
    rw [show clbZ 733 = 65971 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.5971 < Real.log 733 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 733)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.5971)
      (by norm_num : (0.5971 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.5971) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.5971 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.5971)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.5971) * 10 ^ 4 < Real.log 733 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_739 : ((clbZ 739 : ℕ) : ℝ) < Real.log 739 * 10 ^ 4 := by
  have hM : ((clbZ 739 : ℕ) : ℝ) = ((6 : ℝ) + 0.6052) * 10 ^ 4 := by
    rw [show clbZ 739 = 66052 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6052 < Real.log 739 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 739)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6052)
      (by norm_num : (0.6052 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6052) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6052 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6052)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6052) * 10 ^ 4 < Real.log 739 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_743 : ((clbZ 743 : ℕ) : ℝ) < Real.log 743 * 10 ^ 4 := by
  have hM : ((clbZ 743 : ℕ) : ℝ) = ((6 : ℝ) + 0.6106) * 10 ^ 4 := by
    rw [show clbZ 743 = 66106 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6106 < Real.log 743 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 743)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6106)
      (by norm_num : (0.6106 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6106) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6106 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6106)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6106) * 10 ^ 4 < Real.log 743 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_751 : ((clbZ 751 : ℕ) : ℝ) < Real.log 751 * 10 ^ 4 := by
  have hM : ((clbZ 751 : ℕ) : ℝ) = ((6 : ℝ) + 0.6214) * 10 ^ 4 := by
    rw [show clbZ 751 = 66214 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6214 < Real.log 751 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 751)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6214)
      (by norm_num : (0.6214 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6214) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6214 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6214)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6214) * 10 ^ 4 < Real.log 751 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_757 : ((clbZ 757 : ℕ) : ℝ) < Real.log 757 * 10 ^ 4 := by
  have hM : ((clbZ 757 : ℕ) : ℝ) = ((6 : ℝ) + 0.6293) * 10 ^ 4 := by
    rw [show clbZ 757 = 66293 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6293 < Real.log 757 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 757)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6293)
      (by norm_num : (0.6293 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6293) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6293 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6293)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6293) * 10 ^ 4 < Real.log 757 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_761 : ((clbZ 761 : ℕ) : ℝ) < Real.log 761 * 10 ^ 4 := by
  have hM : ((clbZ 761 : ℕ) : ℝ) = ((6 : ℝ) + 0.6346) * 10 ^ 4 := by
    rw [show clbZ 761 = 66346 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6346 < Real.log 761 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 761)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6346)
      (by norm_num : (0.6346 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6346) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6346 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6346)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6346) * 10 ^ 4 < Real.log 761 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_769 : ((clbZ 769 : ℕ) : ℝ) < Real.log 769 * 10 ^ 4 := by
  have hM : ((clbZ 769 : ℕ) : ℝ) = ((6 : ℝ) + 0.6450) * 10 ^ 4 := by
    rw [show clbZ 769 = 66450 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6450 < Real.log 769 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 769)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6450)
      (by norm_num : (0.6450 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6450) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6450 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6450)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6450) * 10 ^ 4 < Real.log 769 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_773 : ((clbZ 773 : ℕ) : ℝ) < Real.log 773 * 10 ^ 4 := by
  have hM : ((clbZ 773 : ℕ) : ℝ) = ((6 : ℝ) + 0.6502) * 10 ^ 4 := by
    rw [show clbZ 773 = 66502 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6502 < Real.log 773 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 773)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6502)
      (by norm_num : (0.6502 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6502) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6502 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6502)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6502) * 10 ^ 4 < Real.log 773 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_787 : ((clbZ 787 : ℕ) : ℝ) < Real.log 787 * 10 ^ 4 := by
  have hM : ((clbZ 787 : ℕ) : ℝ) = ((6 : ℝ) + 0.6682) * 10 ^ 4 := by
    rw [show clbZ 787 = 66682 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6682 < Real.log 787 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 787)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6682)
      (by norm_num : (0.6682 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6682) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6682 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6682)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6682) * 10 ^ 4 < Real.log 787 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_797 : ((clbZ 797 : ℕ) : ℝ) < Real.log 797 * 10 ^ 4 := by
  have hM : ((clbZ 797 : ℕ) : ℝ) = ((6 : ℝ) + 0.6808) * 10 ^ 4 := by
    rw [show clbZ 797 = 66808 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6808 < Real.log 797 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 797)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6808)
      (by norm_num : (0.6808 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6808) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6808 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6808)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6808) * 10 ^ 4 < Real.log 797 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_809 : ((clbZ 809 : ℕ) : ℝ) < Real.log 809 * 10 ^ 4 := by
  have hM : ((clbZ 809 : ℕ) : ℝ) = ((6 : ℝ) + 0.6957) * 10 ^ 4 := by
    rw [show clbZ 809 = 66957 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6957 < Real.log 809 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 809)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6957)
      (by norm_num : (0.6957 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6957) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6957 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6957)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6957) * 10 ^ 4 < Real.log 809 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_811 : ((clbZ 811 : ℕ) : ℝ) < Real.log 811 * 10 ^ 4 := by
  have hM : ((clbZ 811 : ℕ) : ℝ) = ((6 : ℝ) + 0.6982) * 10 ^ 4 := by
    rw [show clbZ 811 = 66982 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.6982 < Real.log 811 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 811)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.6982)
      (by norm_num : (0.6982 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.6982) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.6982 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.6982)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.6982) * 10 ^ 4 < Real.log 811 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_821 : ((clbZ 821 : ℕ) : ℝ) < Real.log 821 * 10 ^ 4 := by
  have hM : ((clbZ 821 : ℕ) : ℝ) = ((6 : ℝ) + 0.7105) * 10 ^ 4 := by
    rw [show clbZ 821 = 67105 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7105 < Real.log 821 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 821)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7105)
      (by norm_num : (0.7105 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7105) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7105 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7105)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7105) * 10 ^ 4 < Real.log 821 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_823 : ((clbZ 823 : ℕ) : ℝ) < Real.log 823 * 10 ^ 4 := by
  have hM : ((clbZ 823 : ℕ) : ℝ) = ((6 : ℝ) + 0.7129) * 10 ^ 4 := by
    rw [show clbZ 823 = 67129 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7129 < Real.log 823 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 823)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7129)
      (by norm_num : (0.7129 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7129) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7129 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7129)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7129) * 10 ^ 4 < Real.log 823 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_827 : ((clbZ 827 : ℕ) : ℝ) < Real.log 827 * 10 ^ 4 := by
  have hM : ((clbZ 827 : ℕ) : ℝ) = ((6 : ℝ) + 0.7178) * 10 ^ 4 := by
    rw [show clbZ 827 = 67178 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7178 < Real.log 827 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 827)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7178)
      (by norm_num : (0.7178 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7178) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7178 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7178)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7178) * 10 ^ 4 < Real.log 827 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_829 : ((clbZ 829 : ℕ) : ℝ) < Real.log 829 * 10 ^ 4 := by
  have hM : ((clbZ 829 : ℕ) : ℝ) = ((6 : ℝ) + 0.7202) * 10 ^ 4 := by
    rw [show clbZ 829 = 67202 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7202 < Real.log 829 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 829)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7202)
      (by norm_num : (0.7202 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7202) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7202 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7202)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7202) * 10 ^ 4 < Real.log 829 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_839 : ((clbZ 839 : ℕ) : ℝ) < Real.log 839 * 10 ^ 4 := by
  have hM : ((clbZ 839 : ℕ) : ℝ) = ((6 : ℝ) + 0.7322) * 10 ^ 4 := by
    rw [show clbZ 839 = 67322 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7322 < Real.log 839 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 839)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7322)
      (by norm_num : (0.7322 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7322) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7322 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7322)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7322) * 10 ^ 4 < Real.log 839 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_853 : ((clbZ 853 : ℕ) : ℝ) < Real.log 853 * 10 ^ 4 := by
  have hM : ((clbZ 853 : ℕ) : ℝ) = ((6 : ℝ) + 0.7487) * 10 ^ 4 := by
    rw [show clbZ 853 = 67487 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7487 < Real.log 853 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 853)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7487)
      (by norm_num : (0.7487 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7487) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7487 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7487)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7487) * 10 ^ 4 < Real.log 853 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_857 : ((clbZ 857 : ℕ) : ℝ) < Real.log 857 * 10 ^ 4 := by
  have hM : ((clbZ 857 : ℕ) : ℝ) = ((6 : ℝ) + 0.7534) * 10 ^ 4 := by
    rw [show clbZ 857 = 67534 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7534 < Real.log 857 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 857)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7534)
      (by norm_num : (0.7534 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7534) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7534 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7534)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7534) * 10 ^ 4 < Real.log 857 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_859 : ((clbZ 859 : ℕ) : ℝ) < Real.log 859 * 10 ^ 4 := by
  have hM : ((clbZ 859 : ℕ) : ℝ) = ((6 : ℝ) + 0.7557) * 10 ^ 4 := by
    rw [show clbZ 859 = 67557 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7557 < Real.log 859 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 859)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7557)
      (by norm_num : (0.7557 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7557) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7557 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7557)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7557) * 10 ^ 4 < Real.log 859 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_863 : ((clbZ 863 : ℕ) : ℝ) < Real.log 863 * 10 ^ 4 := by
  have hM : ((clbZ 863 : ℕ) : ℝ) = ((6 : ℝ) + 0.7604) * 10 ^ 4 := by
    rw [show clbZ 863 = 67604 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7604 < Real.log 863 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 863)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7604)
      (by norm_num : (0.7604 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7604) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7604 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7604)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7604) * 10 ^ 4 < Real.log 863 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_877 : ((clbZ 877 : ℕ) : ℝ) < Real.log 877 * 10 ^ 4 := by
  have hM : ((clbZ 877 : ℕ) : ℝ) = ((6 : ℝ) + 0.7765) * 10 ^ 4 := by
    rw [show clbZ 877 = 67765 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7765 < Real.log 877 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 877)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7765)
      (by norm_num : (0.7765 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7765) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7765 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7765)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7765) * 10 ^ 4 < Real.log 877 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_881 : ((clbZ 881 : ℕ) : ℝ) < Real.log 881 * 10 ^ 4 := by
  have hM : ((clbZ 881 : ℕ) : ℝ) = ((6 : ℝ) + 0.7810) * 10 ^ 4 := by
    rw [show clbZ 881 = 67810 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7810 < Real.log 881 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 881)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7810)
      (by norm_num : (0.7810 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7810) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7810 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7810)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7810) * 10 ^ 4 < Real.log 881 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_883 : ((clbZ 883 : ℕ) : ℝ) < Real.log 883 * 10 ^ 4 := by
  have hM : ((clbZ 883 : ℕ) : ℝ) = ((6 : ℝ) + 0.7833) * 10 ^ 4 := by
    rw [show clbZ 883 = 67833 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7833 < Real.log 883 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 883)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7833)
      (by norm_num : (0.7833 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7833) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7833 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7833)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7833) * 10 ^ 4 < Real.log 883 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_887 : ((clbZ 887 : ℕ) : ℝ) < Real.log 887 * 10 ^ 4 := by
  have hM : ((clbZ 887 : ℕ) : ℝ) = ((6 : ℝ) + 0.7878) * 10 ^ 4 := by
    rw [show clbZ 887 = 67878 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.7878 < Real.log 887 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 887)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7878)
      (by norm_num : (0.7878 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.7878) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.7878 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.7878)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.7878) * 10 ^ 4 < Real.log 887 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_907 : ((clbZ 907 : ℕ) : ℝ) < Real.log 907 * 10 ^ 4 := by
  have hM : ((clbZ 907 : ℕ) : ℝ) = ((6 : ℝ) + 0.8101) * 10 ^ 4 := by
    rw [show clbZ 907 = 68101 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8101 < Real.log 907 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 907)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8101)
      (by norm_num : (0.8101 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8101) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8101 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8101)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8101) * 10 ^ 4 < Real.log 907 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_911 : ((clbZ 911 : ℕ) : ℝ) < Real.log 911 * 10 ^ 4 := by
  have hM : ((clbZ 911 : ℕ) : ℝ) = ((6 : ℝ) + 0.8145) * 10 ^ 4 := by
    rw [show clbZ 911 = 68145 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8145 < Real.log 911 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 911)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8145)
      (by norm_num : (0.8145 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8145) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8145 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8145)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8145) * 10 ^ 4 < Real.log 911 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_919 : ((clbZ 919 : ℕ) : ℝ) < Real.log 919 * 10 ^ 4 := by
  have hM : ((clbZ 919 : ℕ) : ℝ) = ((6 : ℝ) + 0.8232) * 10 ^ 4 := by
    rw [show clbZ 919 = 68232 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8232 < Real.log 919 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 919)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8232)
      (by norm_num : (0.8232 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8232) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8232 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8232)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8232) * 10 ^ 4 < Real.log 919 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_929 : ((clbZ 929 : ℕ) : ℝ) < Real.log 929 * 10 ^ 4 := by
  have hM : ((clbZ 929 : ℕ) : ℝ) = ((6 : ℝ) + 0.8341) * 10 ^ 4 := by
    rw [show clbZ 929 = 68341 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8341 < Real.log 929 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 929)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8341)
      (by norm_num : (0.8341 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8341) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8341 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8341)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8341) * 10 ^ 4 < Real.log 929 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_937 : ((clbZ 937 : ℕ) : ℝ) < Real.log 937 * 10 ^ 4 := by
  have hM : ((clbZ 937 : ℕ) : ℝ) = ((6 : ℝ) + 0.8426) * 10 ^ 4 := by
    rw [show clbZ 937 = 68426 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8426 < Real.log 937 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 937)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8426)
      (by norm_num : (0.8426 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8426) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8426 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8426)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8426) * 10 ^ 4 < Real.log 937 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_941 : ((clbZ 941 : ℕ) : ℝ) < Real.log 941 * 10 ^ 4 := by
  have hM : ((clbZ 941 : ℕ) : ℝ) = ((6 : ℝ) + 0.8469) * 10 ^ 4 := by
    rw [show clbZ 941 = 68469 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8469 < Real.log 941 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 941)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8469)
      (by norm_num : (0.8469 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8469) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8469 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8469)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8469) * 10 ^ 4 < Real.log 941 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_947 : ((clbZ 947 : ℕ) : ℝ) < Real.log 947 * 10 ^ 4 := by
  have hM : ((clbZ 947 : ℕ) : ℝ) = ((6 : ℝ) + 0.8532) * 10 ^ 4 := by
    rw [show clbZ 947 = 68532 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8532 < Real.log 947 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 947)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8532)
      (by norm_num : (0.8532 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8532) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8532 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8532)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8532) * 10 ^ 4 < Real.log 947 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_953 : ((clbZ 953 : ℕ) : ℝ) < Real.log 953 * 10 ^ 4 := by
  have hM : ((clbZ 953 : ℕ) : ℝ) = ((6 : ℝ) + 0.8596) * 10 ^ 4 := by
    rw [show clbZ 953 = 68596 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8596 < Real.log 953 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 953)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8596)
      (by norm_num : (0.8596 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8596) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8596 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8596)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8596) * 10 ^ 4 < Real.log 953 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_967 : ((clbZ 967 : ℕ) : ℝ) < Real.log 967 * 10 ^ 4 := by
  have hM : ((clbZ 967 : ℕ) : ℝ) = ((6 : ℝ) + 0.8741) * 10 ^ 4 := by
    rw [show clbZ 967 = 68741 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8741 < Real.log 967 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 967)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8741)
      (by norm_num : (0.8741 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8741) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8741 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8741)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8741) * 10 ^ 4 < Real.log 967 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_971 : ((clbZ 971 : ℕ) : ℝ) < Real.log 971 * 10 ^ 4 := by
  have hM : ((clbZ 971 : ℕ) : ℝ) = ((6 : ℝ) + 0.8783) * 10 ^ 4 := by
    rw [show clbZ 971 = 68783 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8783 < Real.log 971 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 971)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8783)
      (by norm_num : (0.8783 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8783) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8783 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8783)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8783) * 10 ^ 4 < Real.log 971 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)

lemma clb_log_977 : ((clbZ 977 : ℕ) : ℝ) < Real.log 977 * 10 ^ 4 := by
  have hM : ((clbZ 977 : ℕ) : ℝ) = ((6 : ℝ) + 0.8844) * 10 ^ 4 := by
    rw [show clbZ 977 = 68844 by decide]
    norm_num
  rw [hM]
  have hexp : (6 : ℝ) + 0.8844 < Real.log 977 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 977)]
    have hm : Real.exp (6 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.8844)
      (by norm_num : (0.8844 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((6 : ℝ) + 0.8844) ≤ (2.7182818286 : ℝ) ^ 6 * Real.exp 0.8844 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.8844)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 6)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((6 : ℝ) + 0.8844) * 10 ^ 4 < Real.log 977 * 10 ^ 4 :=
    mul_lt_mul_of_pos_right hexp (by norm_num)


theorem solution (p : ℕ) (hp : p ∈ plist3) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by
  have hmem := hp
  simp only [plist3, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    exact clb_log_607
  · rw [h]
    exact clb_log_613
  · rw [h]
    exact clb_log_617
  · rw [h]
    exact clb_log_619
  · rw [h]
    exact clb_log_631
  · rw [h]
    exact clb_log_641
  · rw [h]
    exact clb_log_643
  · rw [h]
    exact clb_log_647
  · rw [h]
    exact clb_log_653
  · rw [h]
    exact clb_log_659
  · rw [h]
    exact clb_log_661
  · rw [h]
    exact clb_log_673
  · rw [h]
    exact clb_log_677
  · rw [h]
    exact clb_log_683
  · rw [h]
    exact clb_log_691
  · rw [h]
    exact clb_log_701
  · rw [h]
    exact clb_log_709
  · rw [h]
    exact clb_log_719
  · rw [h]
    exact clb_log_727
  · rw [h]
    exact clb_log_733
  · rw [h]
    exact clb_log_739
  · rw [h]
    exact clb_log_743
  · rw [h]
    exact clb_log_751
  · rw [h]
    exact clb_log_757
  · rw [h]
    exact clb_log_761
  · rw [h]
    exact clb_log_769
  · rw [h]
    exact clb_log_773
  · rw [h]
    exact clb_log_787
  · rw [h]
    exact clb_log_797
  · rw [h]
    exact clb_log_809
  · rw [h]
    exact clb_log_811
  · rw [h]
    exact clb_log_821
  · rw [h]
    exact clb_log_823
  · rw [h]
    exact clb_log_827
  · rw [h]
    exact clb_log_829
  · rw [h]
    exact clb_log_839
  · rw [h]
    exact clb_log_853
  · rw [h]
    exact clb_log_857
  · rw [h]
    exact clb_log_859
  · rw [h]
    exact clb_log_863
  · rw [h]
    exact clb_log_877
  · rw [h]
    exact clb_log_881
  · rw [h]
    exact clb_log_883
  · rw [h]
    exact clb_log_887
  · rw [h]
    exact clb_log_907
  · rw [h]
    exact clb_log_911
  · rw [h]
    exact clb_log_919
  · rw [h]
    exact clb_log_929
  · rw [h]
    exact clb_log_937
  · rw [h]
    exact clb_log_941
  · rw [h]
    exact clb_log_947
  · rw [h]
    exact clb_log_953
  · rw [h]
    exact clb_log_967
  · rw [h]
    exact clb_log_971
  · rw [h]
    exact clb_log_977

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (p : ℕ) (hp : p ∈ plist3) :
    ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 :=
  TaoFivePrimes.solution p hp
