-- Prove2me | solution 1 for TaoFivePrimes.log_le_lub
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T12:57:44.264784+00:00
-- url     : https://prove2.me/submissions/a0f6f045-25ac-4d88-9474-375b9621be2b

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma log_le_taylor (x : ℝ) (hx : 0 < x) (hy : |1 - x| ≤ 1/2) :
    Real.log x ≤ -(∑ i ∈ Finset.range 16, (1 - x)^(i+1)/(i+1)) + (1/2)^16 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 - x) (lt_of_le_of_lt hy (by norm_num)) 16
  have h1x : 1 - (1 - x) = x := by ring
  rw [h1x] at h
  have hnum : |1 - x| ^ (16+1) ≤ (1/2)^(16+1) := pow_le_pow_left₀ (abs_nonneg _) hy _
  have hden : (1:ℝ)/2 ≤ 1 - |1 - x| := by linarith [abs_nonneg (1 - x)]
  have hpos1 : (0:ℝ) < 1 - |1 - x| := by linarith
  have hb : |1 - x| ^ (16+1) / (1 - |1 - x|) ≤ (1/2)^16 := by
    rw [div_le_iff₀ hpos1]
    calc |1 - x|^(16+1) ≤ (1/2)^(16+1) := hnum
      _ = (1/2)^16 * (1/2) := by ring
      _ ≤ (1/2)^16 * (1 - |1 - x|) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
  obtain ⟨hlow, hhigh⟩ := abs_le.mp h
  have hhigh' : (∑ i ∈ Finset.range 16, (1-x)^(i+1)/(i+1)) + Real.log x ≤ (1/2)^16 :=
    le_trans hhigh hb
  linarith


end TaoFivePrimes

open TaoFivePrimes

theorem solution (p : Nat) (hp : p ∈ pl521) :
    Real.log (p : Real) ≤ (lub p : Real) := by
  simp only [pl521, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hser := log_le_taylor (1/1 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (1/1 : Real))^(i+1)/(i+1)) + (1/2)^16 + (1:Real)*(6931471808/10000000000 : Real) ≤ (lub 2 : Real) := by
      norm_num [show lub 2 = (693163/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((2 : Nat) : Real) = Real.log (1/1 : Real) + 1 * Real.log 2 := by
      calc Real.log ((2 : Nat) : Real) = Real.log ((1/1 : Real) * (2:Real)^1) := by
            rw [show ((2 : Nat) : Real) = (1/1 : Real) * (2:Real)^1 by norm_num]
        _ = Real.log (1/1 : Real) + Real.log ((2:Real)^1) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (1/1 : Real) + 1 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * Real.log 2 ≤ (1:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (1/1 : Real) + (1:Real) * Real.log 2 ≤ (lub 2 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (3/4 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (3/4 : Real))^(i+1)/(i+1)) + (1/2)^16 + (2:Real)*(6931471808/10000000000 : Real) ≤ (lub 3 : Real) := by
      norm_num [show lub 3 = (274657/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((3 : Nat) : Real) = Real.log (3/4 : Real) + 2 * Real.log 2 := by
      calc Real.log ((3 : Nat) : Real) = Real.log ((3/4 : Real) * (2:Real)^2) := by
            rw [show ((3 : Nat) : Real) = (3/4 : Real) * (2:Real)^2 by norm_num]
        _ = Real.log (3/4 : Real) + Real.log ((2:Real)^2) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (3/4 : Real) + 2 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * Real.log 2 ≤ (2:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (3/4 : Real) + (2:Real) * Real.log 2 ≤ (lub 3 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (5/4 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (5/4 : Real))^(i+1)/(i+1)) + (1/2)^16 + (2:Real)*(6931471808/10000000000 : Real) ≤ (lub 5 : Real) := by
      norm_num [show lub 5 = (804727/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((5 : Nat) : Real) = Real.log (5/4 : Real) + 2 * Real.log 2 := by
      calc Real.log ((5 : Nat) : Real) = Real.log ((5/4 : Real) * (2:Real)^2) := by
            rw [show ((5 : Nat) : Real) = (5/4 : Real) * (2:Real)^2 by norm_num]
        _ = Real.log (5/4 : Real) + Real.log ((2:Real)^2) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (5/4 : Real) + 2 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * Real.log 2 ≤ (2:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (5/4 : Real) + (2:Real) * Real.log 2 ≤ (lub 5 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (7/8 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (7/8 : Real))^(i+1)/(i+1)) + (1/2)^16 + (3:Real)*(6931471808/10000000000 : Real) ≤ (lub 7 : Real) := by
      norm_num [show lub 7 = (972963/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((7 : Nat) : Real) = Real.log (7/8 : Real) + 3 * Real.log 2 := by
      calc Real.log ((7 : Nat) : Real) = Real.log ((7/8 : Real) * (2:Real)^3) := by
            rw [show ((7 : Nat) : Real) = (7/8 : Real) * (2:Real)^3 by norm_num]
        _ = Real.log (7/8 : Real) + Real.log ((2:Real)^3) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (7/8 : Real) + 3 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * Real.log 2 ≤ (3:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (7/8 : Real) + (3:Real) * Real.log 2 ≤ (lub 7 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (11/8 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (11/8 : Real))^(i+1)/(i+1)) + (1/2)^16 + (3:Real)*(6931471808/10000000000 : Real) ≤ (lub 11 : Real) := by
      norm_num [show lub 11 = (2397911/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((11 : Nat) : Real) = Real.log (11/8 : Real) + 3 * Real.log 2 := by
      calc Real.log ((11 : Nat) : Real) = Real.log ((11/8 : Real) * (2:Real)^3) := by
            rw [show ((11 : Nat) : Real) = (11/8 : Real) * (2:Real)^3 by norm_num]
        _ = Real.log (11/8 : Real) + Real.log ((2:Real)^3) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (11/8 : Real) + 3 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * Real.log 2 ≤ (3:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (11/8 : Real) + (3:Real) * Real.log 2 ≤ (lub 11 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (13/16 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (13/16 : Real))^(i+1)/(i+1)) + (1/2)^16 + (4:Real)*(6931471808/10000000000 : Real) ≤ (lub 13 : Real) := by
      norm_num [show lub 13 = (512993/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((13 : Nat) : Real) = Real.log (13/16 : Real) + 4 * Real.log 2 := by
      calc Real.log ((13 : Nat) : Real) = Real.log ((13/16 : Real) * (2:Real)^4) := by
            rw [show ((13 : Nat) : Real) = (13/16 : Real) * (2:Real)^4 by norm_num]
        _ = Real.log (13/16 : Real) + Real.log ((2:Real)^4) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (13/16 : Real) + 4 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (4:Real) * Real.log 2 ≤ (4:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (13/16 : Real) + (4:Real) * Real.log 2 ≤ (lub 13 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (17/16 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (17/16 : Real))^(i+1)/(i+1)) + (1/2)^16 + (4:Real)*(6931471808/10000000000 : Real) ≤ (lub 17 : Real) := by
      norm_num [show lub 17 = (2833229/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((17 : Nat) : Real) = Real.log (17/16 : Real) + 4 * Real.log 2 := by
      calc Real.log ((17 : Nat) : Real) = Real.log ((17/16 : Real) * (2:Real)^4) := by
            rw [show ((17 : Nat) : Real) = (17/16 : Real) * (2:Real)^4 by norm_num]
        _ = Real.log (17/16 : Real) + Real.log ((2:Real)^4) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (17/16 : Real) + 4 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (4:Real) * Real.log 2 ≤ (4:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (17/16 : Real) + (4:Real) * Real.log 2 ≤ (lub 17 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (19/16 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (19/16 : Real))^(i+1)/(i+1)) + (1/2)^16 + (4:Real)*(6931471808/10000000000 : Real) ≤ (lub 19 : Real) := by
      norm_num [show lub 19 = (588891/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((19 : Nat) : Real) = Real.log (19/16 : Real) + 4 * Real.log 2 := by
      calc Real.log ((19 : Nat) : Real) = Real.log ((19/16 : Real) * (2:Real)^4) := by
            rw [show ((19 : Nat) : Real) = (19/16 : Real) * (2:Real)^4 by norm_num]
        _ = Real.log (19/16 : Real) + Real.log ((2:Real)^4) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (19/16 : Real) + 4 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (4:Real) * Real.log 2 ≤ (4:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (19/16 : Real) + (4:Real) * Real.log 2 ≤ (lub 19 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (23/16 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (23/16 : Real))^(i+1)/(i+1)) + (1/2)^16 + (4:Real)*(6931471808/10000000000 : Real) ≤ (lub 23 : Real) := by
      norm_num [show lub 23 = (313551/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((23 : Nat) : Real) = Real.log (23/16 : Real) + 4 * Real.log 2 := by
      calc Real.log ((23 : Nat) : Real) = Real.log ((23/16 : Real) * (2:Real)^4) := by
            rw [show ((23 : Nat) : Real) = (23/16 : Real) * (2:Real)^4 by norm_num]
        _ = Real.log (23/16 : Real) + Real.log ((2:Real)^4) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (23/16 : Real) + 4 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (4:Real) * Real.log 2 ≤ (4:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (23/16 : Real) + (4:Real) * Real.log 2 ≤ (lub 23 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (29/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (29/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 29 : Real) := by
      norm_num [show lub 29 = (210457/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((29 : Nat) : Real) = Real.log (29/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((29 : Nat) : Real) = Real.log ((29/32 : Real) * (2:Real)^5) := by
            rw [show ((29 : Nat) : Real) = (29/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (29/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (29/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (29/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 29 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (31/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (31/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 31 : Real) := by
      norm_num [show lub 31 = (3434003/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((31 : Nat) : Real) = Real.log (31/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((31 : Nat) : Real) = Real.log ((31/32 : Real) * (2:Real)^5) := by
            rw [show ((31 : Nat) : Real) = (31/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (31/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (31/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (31/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 31 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (37/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (37/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 37 : Real) := by
      norm_num [show lub 37 = (1805467/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((37 : Nat) : Real) = Real.log (37/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((37 : Nat) : Real) = Real.log ((37/32 : Real) * (2:Real)^5) := by
            rw [show ((37 : Nat) : Real) = (37/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (37/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (37/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (37/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 37 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (41/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (41/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 41 : Real) := by
      norm_num [show lub 41 = (928397/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((41 : Nat) : Real) = Real.log (41/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((41 : Nat) : Real) = Real.log ((41/32 : Real) * (2:Real)^5) := by
            rw [show ((41 : Nat) : Real) = (41/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (41/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (41/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (41/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 41 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (43/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (43/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 43 : Real) := by
      norm_num [show lub 43 = (58769/15625) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((43 : Nat) : Real) = Real.log (43/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((43 : Nat) : Real) = Real.log ((43/32 : Real) * (2:Real)^5) := by
            rw [show ((43 : Nat) : Real) = (43/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (43/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (43/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (43/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 43 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (47/32 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (47/32 : Real))^(i+1)/(i+1)) + (1/2)^16 + (5:Real)*(6931471808/10000000000 : Real) ≤ (lub 47 : Real) := by
      norm_num [show lub 47 = (3850163/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((47 : Nat) : Real) = Real.log (47/32 : Real) + 5 * Real.log 2 := by
      calc Real.log ((47 : Nat) : Real) = Real.log ((47/32 : Real) * (2:Real)^5) := by
            rw [show ((47 : Nat) : Real) = (47/32 : Real) * (2:Real)^5 by norm_num]
        _ = Real.log (47/32 : Real) + Real.log ((2:Real)^5) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (47/32 : Real) + 5 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (5:Real) * Real.log 2 ≤ (5:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (47/32 : Real) + (5:Real) * Real.log 2 ≤ (lub 47 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (53/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (53/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 53 : Real) := by
      norm_num [show lub 53 = (992577/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((53 : Nat) : Real) = Real.log (53/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((53 : Nat) : Real) = Real.log ((53/64 : Real) * (2:Real)^6) := by
            rw [show ((53 : Nat) : Real) = (53/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (53/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (53/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (53/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 53 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (59/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (59/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 59 : Real) := by
      norm_num [show lub 59 = (4077553/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((59 : Nat) : Real) = Real.log (59/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((59 : Nat) : Real) = Real.log ((59/64 : Real) * (2:Real)^6) := by
            rw [show ((59 : Nat) : Real) = (59/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (59/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (59/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (59/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 59 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (61/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (61/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 61 : Real) := by
      norm_num [show lub 61 = (411089/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((61 : Nat) : Real) = Real.log (61/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((61 : Nat) : Real) = Real.log ((61/64 : Real) * (2:Real)^6) := by
            rw [show ((61 : Nat) : Real) = (61/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (61/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (61/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (61/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 61 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (67/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (67/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 67 : Real) := by
      norm_num [show lub 67 = (1051177/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((67 : Nat) : Real) = Real.log (67/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((67 : Nat) : Real) = Real.log ((67/64 : Real) * (2:Real)^6) := by
            rw [show ((67 : Nat) : Real) = (67/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (67/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (67/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (67/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 67 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (71/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (71/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 71 : Real) := by
      norm_num [show lub 71 = (532837/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((71 : Nat) : Real) = Real.log (71/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((71 : Nat) : Real) = Real.log ((71/64 : Real) * (2:Real)^6) := by
            rw [show ((71 : Nat) : Real) = (71/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (71/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (71/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (71/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 71 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (73/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (73/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 73 : Real) := by
      norm_num [show lub 73 = (171619/40000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((73 : Nat) : Real) = Real.log (73/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((73 : Nat) : Real) = Real.log ((73/64 : Real) * (2:Real)^6) := by
            rw [show ((73 : Nat) : Real) = (73/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (73/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (73/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (73/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 73 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (79/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (79/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 79 : Real) := by
      norm_num [show lub 79 = (546183/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((79 : Nat) : Real) = Real.log (79/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((79 : Nat) : Real) = Real.log ((79/64 : Real) * (2:Real)^6) := by
            rw [show ((79 : Nat) : Real) = (79/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (79/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (79/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (79/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 79 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (83/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (83/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 83 : Real) := by
      norm_num [show lub 83 = (552357/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((83 : Nat) : Real) = Real.log (83/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((83 : Nat) : Real) = Real.log ((83/64 : Real) * (2:Real)^6) := by
            rw [show ((83 : Nat) : Real) = (83/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (83/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (83/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (83/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 83 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (89/64 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (89/64 : Real))^(i+1)/(i+1)) + (1/2)^16 + (6:Real)*(6931471808/10000000000 : Real) ≤ (lub 89 : Real) := by
      norm_num [show lub 89 = (1122163/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((89 : Nat) : Real) = Real.log (89/64 : Real) + 6 * Real.log 2 := by
      calc Real.log ((89 : Nat) : Real) = Real.log ((89/64 : Real) * (2:Real)^6) := by
            rw [show ((89 : Nat) : Real) = (89/64 : Real) * (2:Real)^6 by norm_num]
        _ = Real.log (89/64 : Real) + Real.log ((2:Real)^6) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (89/64 : Real) + 6 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (6:Real) * Real.log 2 ≤ (6:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (89/64 : Real) + (6:Real) * Real.log 2 ≤ (lub 89 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (97/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (97/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 97 : Real) := by
      norm_num [show lub 97 = (4574727/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((97 : Nat) : Real) = Real.log (97/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((97 : Nat) : Real) = Real.log ((97/128 : Real) * (2:Real)^7) := by
            rw [show ((97 : Nat) : Real) = (97/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (97/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (97/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (97/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 97 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (101/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (101/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 101 : Real) := by
      norm_num [show lub 101 = (144223/31250) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((101 : Nat) : Real) = Real.log (101/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((101 : Nat) : Real) = Real.log ((101/128 : Real) * (2:Real)^7) := by
            rw [show ((101 : Nat) : Real) = (101/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (101/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (101/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (101/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 101 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (103/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (103/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 103 : Real) := by
      norm_num [show lub 103 = (926949/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((103 : Nat) : Real) = Real.log (103/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((103 : Nat) : Real) = Real.log ((103/128 : Real) * (2:Real)^7) := by
            rw [show ((103 : Nat) : Real) = (103/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (103/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (103/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (103/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 103 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (107/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (107/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 107 : Real) := by
      norm_num [show lub 107 = (934569/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((107 : Nat) : Real) = Real.log (107/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((107 : Nat) : Real) = Real.log ((107/128 : Real) * (2:Real)^7) := by
            rw [show ((107 : Nat) : Real) = (107/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (107/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (107/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (107/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 107 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (109/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (109/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 109 : Real) := by
      norm_num [show lub 109 = (1172841/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((109 : Nat) : Real) = Real.log (109/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((109 : Nat) : Real) = Real.log ((109/128 : Real) * (2:Real)^7) := by
            rw [show ((109 : Nat) : Real) = (109/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (109/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (109/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (109/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 109 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (113/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (113/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 113 : Real) := by
      norm_num [show lub 113 = (1181851/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((113 : Nat) : Real) = Real.log (113/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((113 : Nat) : Real) = Real.log ((113/128 : Real) * (2:Real)^7) := by
            rw [show ((113 : Nat) : Real) = (113/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (113/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (113/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (113/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 113 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (127/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (127/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 127 : Real) := by
      norm_num [show lub 127 = (4844203/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((127 : Nat) : Real) = Real.log (127/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((127 : Nat) : Real) = Real.log ((127/128 : Real) * (2:Real)^7) := by
            rw [show ((127 : Nat) : Real) = (127/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (127/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (127/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (127/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 127 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (131/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (131/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 131 : Real) := by
      norm_num [show lub 131 = (4875213/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((131 : Nat) : Real) = Real.log (131/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((131 : Nat) : Real) = Real.log ((131/128 : Real) * (2:Real)^7) := by
            rw [show ((131 : Nat) : Real) = (131/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (131/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (131/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (131/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 131 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (137/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (137/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 137 : Real) := by
      norm_num [show lub 137 = (4919997/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((137 : Nat) : Real) = Real.log (137/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((137 : Nat) : Real) = Real.log ((137/128 : Real) * (2:Real)^7) := by
            rw [show ((137 : Nat) : Real) = (137/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (137/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (137/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (137/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 137 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (139/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (139/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 139 : Real) := by
      norm_num [show lub 139 = (493449/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((139 : Nat) : Real) = Real.log (139/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((139 : Nat) : Real) = Real.log ((139/128 : Real) * (2:Real)^7) := by
            rw [show ((139 : Nat) : Real) = (139/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (139/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (139/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (139/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 139 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (149/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (149/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 149 : Real) := by
      norm_num [show lub 149 = (2501981/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((149 : Nat) : Real) = Real.log (149/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((149 : Nat) : Real) = Real.log ((149/128 : Real) * (2:Real)^7) := by
            rw [show ((149 : Nat) : Real) = (149/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (149/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (149/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (149/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 149 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (151/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (151/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 151 : Real) := by
      norm_num [show lub 151 = (313581/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((151 : Nat) : Real) = Real.log (151/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((151 : Nat) : Real) = Real.log ((151/128 : Real) * (2:Real)^7) := by
            rw [show ((151 : Nat) : Real) = (151/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (151/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (151/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (151/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 151 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (157/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (157/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 157 : Real) := by
      norm_num [show lub 157 = (2528131/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((157 : Nat) : Real) = Real.log (157/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((157 : Nat) : Real) = Real.log ((157/128 : Real) * (2:Real)^7) := by
            rw [show ((157 : Nat) : Real) = (157/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (157/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (157/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (157/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 157 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (163/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (163/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 163 : Real) := by
      norm_num [show lub 163 = (2546883/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((163 : Nat) : Real) = Real.log (163/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((163 : Nat) : Real) = Real.log ((163/128 : Real) * (2:Real)^7) := by
            rw [show ((163 : Nat) : Real) = (163/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (163/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (163/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (163/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 163 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (167/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (167/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 167 : Real) := by
      norm_num [show lub 167 = (511801/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((167 : Nat) : Real) = Real.log (167/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((167 : Nat) : Real) = Real.log ((167/128 : Real) * (2:Real)^7) := by
            rw [show ((167 : Nat) : Real) = (167/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (167/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (167/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (167/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 167 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (173/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (173/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 173 : Real) := by
      norm_num [show lub 173 = (5153307/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((173 : Nat) : Real) = Real.log (173/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((173 : Nat) : Real) = Real.log ((173/128 : Real) * (2:Real)^7) := by
            rw [show ((173 : Nat) : Real) = (173/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (173/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (173/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (173/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 173 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (179/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (179/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 179 : Real) := by
      norm_num [show lub 179 = (2593701/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((179 : Nat) : Real) = Real.log (179/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((179 : Nat) : Real) = Real.log ((179/128 : Real) * (2:Real)^7) := by
            rw [show ((179 : Nat) : Real) = (179/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (179/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (179/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (179/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 179 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (181/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (181/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 181 : Real) := by
      norm_num [show lub 181 = (5198513/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((181 : Nat) : Real) = Real.log (181/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((181 : Nat) : Real) = Real.log ((181/128 : Real) * (2:Real)^7) := by
            rw [show ((181 : Nat) : Real) = (181/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (181/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (181/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (181/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 181 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (191/128 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (191/128 : Real))^(i+1)/(i+1)) + (1/2)^16 + (7:Real)*(6931471808/10000000000 : Real) ≤ (lub 191 : Real) := by
      norm_num [show lub 191 = (5252289/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((191 : Nat) : Real) = Real.log (191/128 : Real) + 7 * Real.log 2 := by
      calc Real.log ((191 : Nat) : Real) = Real.log ((191/128 : Real) * (2:Real)^7) := by
            rw [show ((191 : Nat) : Real) = (191/128 : Real) * (2:Real)^7 by norm_num]
        _ = Real.log (191/128 : Real) + Real.log ((2:Real)^7) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (191/128 : Real) + 7 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (7:Real) * Real.log 2 ≤ (7:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (191/128 : Real) + (7:Real) * Real.log 2 ≤ (lub 191 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (193/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (193/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 193 : Real) := by
      norm_num [show lub 193 = (2631353/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((193 : Nat) : Real) = Real.log (193/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((193 : Nat) : Real) = Real.log ((193/256 : Real) * (2:Real)^8) := by
            rw [show ((193 : Nat) : Real) = (193/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (193/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (193/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (193/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 193 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (197/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (197/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 197 : Real) := by
      norm_num [show lub 197 = (5283219/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((197 : Nat) : Real) = Real.log (197/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((197 : Nat) : Real) = Real.log ((197/256 : Real) * (2:Real)^8) := by
            rw [show ((197 : Nat) : Real) = (197/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (197/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (197/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (197/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 197 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (199/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (199/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 199 : Real) := by
      norm_num [show lub 199 = (5293321/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((199 : Nat) : Real) = Real.log (199/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((199 : Nat) : Real) = Real.log ((199/256 : Real) * (2:Real)^8) := by
            rw [show ((199 : Nat) : Real) = (199/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (199/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (199/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (199/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 199 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (211/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (211/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 211 : Real) := by
      norm_num [show lub 211 = (2675937/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((211 : Nat) : Real) = Real.log (211/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((211 : Nat) : Real) = Real.log ((211/256 : Real) * (2:Real)^8) := by
            rw [show ((211 : Nat) : Real) = (211/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (211/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (211/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (211/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 211 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (223/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (223/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 223 : Real) := by
      norm_num [show lub 223 = (1351797/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((223 : Nat) : Real) = Real.log (223/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((223 : Nat) : Real) = Real.log ((223/256 : Real) * (2:Real)^8) := by
            rw [show ((223 : Nat) : Real) = (223/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (223/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (223/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (223/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 223 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (227/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (227/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 227 : Real) := by
      norm_num [show lub 227 = (2712483/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((227 : Nat) : Real) = Real.log (227/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((227 : Nat) : Real) = Real.log ((227/256 : Real) * (2:Real)^8) := by
            rw [show ((227 : Nat) : Real) = (227/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (227/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (227/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (227/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 227 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (229/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (229/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 229 : Real) := by
      norm_num [show lub 229 = (2716869/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((229 : Nat) : Real) = Real.log (229/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((229 : Nat) : Real) = Real.log ((229/256 : Real) * (2:Real)^8) := by
            rw [show ((229 : Nat) : Real) = (229/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (229/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (229/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (229/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 229 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (233/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (233/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 233 : Real) := by
      norm_num [show lub 233 = (2725527/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((233 : Nat) : Real) = Real.log (233/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((233 : Nat) : Real) = Real.log ((233/256 : Real) * (2:Real)^8) := by
            rw [show ((233 : Nat) : Real) = (233/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (233/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (233/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (233/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 233 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (239/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (239/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 239 : Real) := by
      norm_num [show lub 239 = (5476479/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((239 : Nat) : Real) = Real.log (239/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((239 : Nat) : Real) = Real.log ((239/256 : Real) * (2:Real)^8) := by
            rw [show ((239 : Nat) : Real) = (239/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (239/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (239/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (239/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 239 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (241/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (241/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 241 : Real) := by
      norm_num [show lub 241 = (5484813/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((241 : Nat) : Real) = Real.log (241/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((241 : Nat) : Real) = Real.log ((241/256 : Real) * (2:Real)^8) := by
            rw [show ((241 : Nat) : Real) = (241/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (241/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (241/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (241/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 241 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (251/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (251/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 251 : Real) := by
      norm_num [show lub 251 = (5525469/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((251 : Nat) : Real) = Real.log (251/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((251 : Nat) : Real) = Real.log ((251/256 : Real) * (2:Real)^8) := by
            rw [show ((251 : Nat) : Real) = (251/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (251/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (251/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (251/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 251 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (257/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (257/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 257 : Real) := by
      norm_num [show lub 257 = (1387273/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((257 : Nat) : Real) = Real.log (257/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((257 : Nat) : Real) = Real.log ((257/256 : Real) * (2:Real)^8) := by
            rw [show ((257 : Nat) : Real) = (257/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (257/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (257/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (257/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 257 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (263/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (263/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 263 : Real) := by
      norm_num [show lub 263 = (557217/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((263 : Nat) : Real) = Real.log (263/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((263 : Nat) : Real) = Real.log ((263/256 : Real) * (2:Real)^8) := by
            rw [show ((263 : Nat) : Real) = (263/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (263/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (263/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (263/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 263 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (269/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (269/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 269 : Real) := by
      norm_num [show lub 269 = (5594727/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((269 : Nat) : Real) = Real.log (269/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((269 : Nat) : Real) = Real.log ((269/256 : Real) * (2:Real)^8) := by
            rw [show ((269 : Nat) : Real) = (269/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (269/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (269/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (269/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 269 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (271/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (271/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 271 : Real) := by
      norm_num [show lub 271 = (1120427/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((271 : Nat) : Real) = Real.log (271/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((271 : Nat) : Real) = Real.log ((271/256 : Real) * (2:Real)^8) := by
            rw [show ((271 : Nat) : Real) = (271/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (271/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (271/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (271/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 271 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (277/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (277/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 277 : Real) := by
      norm_num [show lub 277 = (5624033/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((277 : Nat) : Real) = Real.log (277/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((277 : Nat) : Real) = Real.log ((277/256 : Real) * (2:Real)^8) := by
            rw [show ((277 : Nat) : Real) = (277/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (277/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (277/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (277/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 277 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (281/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (281/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 281 : Real) := by
      norm_num [show lub 281 = (563837/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((281 : Nat) : Real) = Real.log (281/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((281 : Nat) : Real) = Real.log ((281/256 : Real) * (2:Real)^8) := by
            rw [show ((281 : Nat) : Real) = (281/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (281/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (281/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (281/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 281 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (283/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (283/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 283 : Real) := by
      norm_num [show lub 283 = (5645463/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((283 : Nat) : Real) = Real.log (283/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((283 : Nat) : Real) = Real.log ((283/256 : Real) * (2:Real)^8) := by
            rw [show ((283 : Nat) : Real) = (283/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (283/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (283/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (283/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 283 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (293/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (293/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 293 : Real) := by
      norm_num [show lub 293 = (1420047/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((293 : Nat) : Real) = Real.log (293/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((293 : Nat) : Real) = Real.log ((293/256 : Real) * (2:Real)^8) := by
            rw [show ((293 : Nat) : Real) = (293/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (293/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (293/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (293/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 293 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (307/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (307/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 307 : Real) := by
      norm_num [show lub 307 = (357929/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((307 : Nat) : Real) = Real.log (307/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((307 : Nat) : Real) = Real.log ((307/256 : Real) * (2:Real)^8) := by
            rw [show ((307 : Nat) : Real) = (307/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (307/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (307/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (307/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 307 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (311/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (311/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 311 : Real) := by
      norm_num [show lub 311 = (5739809/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((311 : Nat) : Real) = Real.log (311/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((311 : Nat) : Real) = Real.log ((311/256 : Real) * (2:Real)^8) := by
            rw [show ((311 : Nat) : Real) = (311/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (311/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (311/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (311/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 311 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (313/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (313/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 313 : Real) := by
      norm_num [show lub 313 = (5746219/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((313 : Nat) : Real) = Real.log (313/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((313 : Nat) : Real) = Real.log ((313/256 : Real) * (2:Real)^8) := by
            rw [show ((313 : Nat) : Real) = (313/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (313/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (313/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (313/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 313 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (317/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (317/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 317 : Real) := by
      norm_num [show lub 317 = (2879459/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((317 : Nat) : Real) = Real.log (317/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((317 : Nat) : Real) = Real.log ((317/256 : Real) * (2:Real)^8) := by
            rw [show ((317 : Nat) : Real) = (317/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (317/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (317/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (317/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 317 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (331/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (331/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 331 : Real) := by
      norm_num [show lub 331 = (2901067/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((331 : Nat) : Real) = Real.log (331/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((331 : Nat) : Real) = Real.log ((331/256 : Real) * (2:Real)^8) := by
            rw [show ((331 : Nat) : Real) = (331/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (331/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (331/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (331/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 331 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (337/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (337/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 337 : Real) := by
      norm_num [show lub 337 = (5820099/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((337 : Nat) : Real) = Real.log (337/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((337 : Nat) : Real) = Real.log ((337/256 : Real) * (2:Real)^8) := by
            rw [show ((337 : Nat) : Real) = (337/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (337/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (337/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (337/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 337 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (347/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (347/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 347 : Real) := by
      norm_num [show lub 347 = (5849341/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((347 : Nat) : Real) = Real.log (347/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((347 : Nat) : Real) = Real.log ((347/256 : Real) * (2:Real)^8) := by
            rw [show ((347 : Nat) : Real) = (347/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (347/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (347/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (347/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 347 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (349/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (349/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 349 : Real) := by
      norm_num [show lub 349 = (365943/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((349 : Nat) : Real) = Real.log (349/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((349 : Nat) : Real) = Real.log ((349/256 : Real) * (2:Real)^8) := by
            rw [show ((349 : Nat) : Real) = (349/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (349/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (349/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (349/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 349 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (353/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (353/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 353 : Real) := by
      norm_num [show lub 353 = (1466621/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((353 : Nat) : Real) = Real.log (353/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((353 : Nat) : Real) = Real.log ((353/256 : Real) * (2:Real)^8) := by
            rw [show ((353 : Nat) : Real) = (353/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (353/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (353/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (353/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 353 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (359/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (359/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 359 : Real) := by
      norm_num [show lub 359 = (2941669/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((359 : Nat) : Real) = Real.log (359/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((359 : Nat) : Real) = Real.log ((359/256 : Real) * (2:Real)^8) := by
            rw [show ((359 : Nat) : Real) = (359/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (359/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (359/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (359/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 359 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (367/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (367/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 367 : Real) := by
      norm_num [show lub 367 = (2952689/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((367 : Nat) : Real) = Real.log (367/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((367 : Nat) : Real) = Real.log ((367/256 : Real) * (2:Real)^8) := by
            rw [show ((367 : Nat) : Real) = (367/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (367/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (367/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (367/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 367 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (373/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (373/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 373 : Real) := by
      norm_num [show lub 373 = (2960797/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((373 : Nat) : Real) = Real.log (373/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((373 : Nat) : Real) = Real.log ((373/256 : Real) * (2:Real)^8) := by
            rw [show ((373 : Nat) : Real) = (373/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (373/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (373/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (373/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 373 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (379/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (379/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 379 : Real) := by
      norm_num [show lub 379 = (371097/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((379 : Nat) : Real) = Real.log (379/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((379 : Nat) : Real) = Real.log ((379/256 : Real) * (2:Real)^8) := by
            rw [show ((379 : Nat) : Real) = (379/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (379/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (379/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (379/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 379 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (383/256 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (383/256 : Real))^(i+1)/(i+1)) + (1/2)^16 + (8:Real)*(6931471808/10000000000 : Real) ≤ (lub 383 : Real) := by
      norm_num [show lub 383 = (118961/20000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((383 : Nat) : Real) = Real.log (383/256 : Real) + 8 * Real.log 2 := by
      calc Real.log ((383 : Nat) : Real) = Real.log ((383/256 : Real) * (2:Real)^8) := by
            rw [show ((383 : Nat) : Real) = (383/256 : Real) * (2:Real)^8 by norm_num]
        _ = Real.log (383/256 : Real) + Real.log ((2:Real)^8) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (383/256 : Real) + 8 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (8:Real) * Real.log 2 ≤ (8:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (383/256 : Real) + (8:Real) * Real.log 2 ≤ (lub 383 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (389/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (389/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 389 : Real) := by
      norm_num [show lub 389 = (1192719/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((389 : Nat) : Real) = Real.log (389/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((389 : Nat) : Real) = Real.log ((389/512 : Real) * (2:Real)^9) := by
            rw [show ((389 : Nat) : Real) = (389/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (389/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (389/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (389/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 389 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (397/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (397/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 397 : Real) := by
      norm_num [show lub 397 = (373997/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((397 : Nat) : Real) = Real.log (397/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((397 : Nat) : Real) = Real.log ((397/512 : Real) * (2:Real)^9) := by
            rw [show ((397 : Nat) : Real) = (397/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (397/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (397/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (397/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 397 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (401/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (401/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 401 : Real) := by
      norm_num [show lub 401 = (5993977/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((401 : Nat) : Real) = Real.log (401/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((401 : Nat) : Real) = Real.log ((401/512 : Real) * (2:Real)^9) := by
            rw [show ((401 : Nat) : Real) = (401/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (401/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (401/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (401/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 401 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (409/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (409/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 409 : Real) := by
      norm_num [show lub 409 = (6013731/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((409 : Nat) : Real) = Real.log (409/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((409 : Nat) : Real) = Real.log ((409/512 : Real) * (2:Real)^9) := by
            rw [show ((409 : Nat) : Real) = (409/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (409/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (409/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (409/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 409 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (419/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (419/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 419 : Real) := by
      norm_num [show lub 419 = (6037887/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((419 : Nat) : Real) = Real.log (419/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((419 : Nat) : Real) = Real.log ((419/512 : Real) * (2:Real)^9) := by
            rw [show ((419 : Nat) : Real) = (419/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (419/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (419/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (419/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 419 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (421/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (421/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 421 : Real) := by
      norm_num [show lub 421 = (6042649/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((421 : Nat) : Real) = Real.log (421/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((421 : Nat) : Real) = Real.log ((421/512 : Real) * (2:Real)^9) := by
            rw [show ((421 : Nat) : Real) = (421/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (421/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (421/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (421/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 421 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (431/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (431/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 431 : Real) := by
      norm_num [show lub 431 = (1516531/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((431 : Nat) : Real) = Real.log (431/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((431 : Nat) : Real) = Real.log ((431/512 : Real) * (2:Real)^9) := by
            rw [show ((431 : Nat) : Real) = (431/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (431/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (431/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (431/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 431 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (433/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (433/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 433 : Real) := by
      norm_num [show lub 433 = (6070753/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((433 : Nat) : Real) = Real.log (433/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((433 : Nat) : Real) = Real.log ((433/512 : Real) * (2:Real)^9) := by
            rw [show ((433 : Nat) : Real) = (433/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (433/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (433/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (433/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 433 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (439/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (439/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 439 : Real) := by
      norm_num [show lub 439 = (1216903/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((439 : Nat) : Real) = Real.log (439/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((439 : Nat) : Real) = Real.log ((439/512 : Real) * (2:Real)^9) := by
            rw [show ((439 : Nat) : Real) = (439/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (439/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (439/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (439/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 439 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (443/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (443/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 443 : Real) := by
      norm_num [show lub 443 = (3046793/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((443 : Nat) : Real) = Real.log (443/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((443 : Nat) : Real) = Real.log ((443/512 : Real) * (2:Real)^9) := by
            rw [show ((443 : Nat) : Real) = (443/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (443/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (443/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (443/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 443 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (449/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (449/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 449 : Real) := by
      norm_num [show lub 449 = (6107039/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((449 : Nat) : Real) = Real.log (449/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((449 : Nat) : Real) = Real.log ((449/512 : Real) * (2:Real)^9) := by
            rw [show ((449 : Nat) : Real) = (449/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (449/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (449/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (449/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 449 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (457/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (457/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 457 : Real) := by
      norm_num [show lub 457 = (6124699/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((457 : Nat) : Real) = Real.log (457/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((457 : Nat) : Real) = Real.log ((457/512 : Real) * (2:Real)^9) := by
            rw [show ((457 : Nat) : Real) = (457/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (457/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (457/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (457/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 457 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (461/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (461/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 461 : Real) := by
      norm_num [show lub 461 = (3066707/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((461 : Nat) : Real) = Real.log (461/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((461 : Nat) : Real) = Real.log ((461/512 : Real) * (2:Real)^9) := by
            rw [show ((461 : Nat) : Real) = (461/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (461/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (461/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (461/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 461 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (463/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (463/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 463 : Real) := by
      norm_num [show lub 463 = (6137743/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((463 : Nat) : Real) = Real.log (463/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((463 : Nat) : Real) = Real.log ((463/512 : Real) * (2:Real)^9) := by
            rw [show ((463 : Nat) : Real) = (463/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (463/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (463/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (463/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 463 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (467/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (467/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 467 : Real) := by
      norm_num [show lub 467 = (1229269/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((467 : Nat) : Real) = Real.log (467/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((467 : Nat) : Real) = Real.log ((467/512 : Real) * (2:Real)^9) := by
            rw [show ((467 : Nat) : Real) = (467/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (467/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (467/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (467/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 467 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (479/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (479/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 479 : Real) := by
      norm_num [show lub 479 = (1542929/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((479 : Nat) : Real) = Real.log (479/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((479 : Nat) : Real) = Real.log ((479/512 : Real) * (2:Real)^9) := by
            rw [show ((479 : Nat) : Real) = (479/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (479/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (479/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (479/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 479 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (487/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (487/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 487 : Real) := by
      norm_num [show lub 487 = (154707/25000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((487 : Nat) : Real) = Real.log (487/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((487 : Nat) : Real) = Real.log ((487/512 : Real) * (2:Real)^9) := by
            rw [show ((487 : Nat) : Real) = (487/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (487/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (487/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (487/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 487 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (491/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (491/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 491 : Real) := by
      norm_num [show lub 491 = (309823/50000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((491 : Nat) : Real) = Real.log (491/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((491 : Nat) : Real) = Real.log ((491/512 : Real) * (2:Real)^9) := by
            rw [show ((491 : Nat) : Real) = (491/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (491/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (491/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (491/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 491 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (499/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (499/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 499 : Real) := by
      norm_num [show lub 499 = (3106311/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((499 : Nat) : Real) = Real.log (499/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((499 : Nat) : Real) = Real.log ((499/512 : Real) * (2:Real)^9) := by
            rw [show ((499 : Nat) : Real) = (499/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (499/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (499/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (499/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 499 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (503/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (503/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 503 : Real) := by
      norm_num [show lub 503 = (3110303/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((503 : Nat) : Real) = Real.log (503/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((503 : Nat) : Real) = Real.log ((503/512 : Real) * (2:Real)^9) := by
            rw [show ((503 : Nat) : Real) = (503/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (503/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (503/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (503/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 503 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (509/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (509/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 509 : Real) := by
      norm_num [show lub 509 = (389529/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((509 : Nat) : Real) = Real.log (509/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((509 : Nat) : Real) = Real.log ((509/512 : Real) * (2:Real)^9) := by
            rw [show ((509 : Nat) : Real) = (509/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (509/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (509/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (509/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 509 : Real) := by linarith
    exact le_trans hdec.le hfin

  · have hser := log_le_taylor (521/512 : Real) (by norm_num) (by norm_num)
    have hnum : -(∑ i ∈ Finset.range 16, (1 - (521/512 : Real))^(i+1)/(i+1)) + (1/2)^16 + (9:Real)*(6931471808/10000000000 : Real) ≤ (lub 521 : Real) := by
      norm_num [show lub 521 = (3127883/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((521 : Nat) : Real) = Real.log (521/512 : Real) + 9 * Real.log 2 := by
      calc Real.log ((521 : Nat) : Real) = Real.log ((521/512 : Real) * (2:Real)^9) := by
            rw [show ((521 : Nat) : Real) = (521/512 : Real) * (2:Real)^9 by norm_num]
        _ = Real.log (521/512 : Real) + Real.log ((2:Real)^9) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log (521/512 : Real) + 9 * Real.log 2 := by
            rw [Real.log_pow]
            ring
    have hlog2 : Real.log 2 < (6931471808/10000000000 : Real) := by
      have hl := Real.log_two_lt_d9
      norm_num at hl
      linarith
    have hmul : (9:Real) * Real.log 2 ≤ (9:Real) * (6931471808/10000000000 : Real) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : Real.log (521/512 : Real) + (9:Real) * Real.log 2 ≤ (lub 521 : Real) := by linarith
    exact le_trans hdec.le hfin


