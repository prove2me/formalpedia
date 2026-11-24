-- Prove2me | solution 1 for TaoFivePrimes.llb_le_loglog
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T12:57:43.480409+00:00
-- url     : https://prove2.me/submissions/c40a12d9-d75e-4040-8021-1be49d4fd5fb

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma le_log_taylor (x : ℝ) (hx : 0 < x) (hy : |1 - x| ≤ 1/2) :
    -(∑ i ∈ Finset.range 16, (1 - x)^(i+1)/(i+1)) - (1/2)^16 ≤ Real.log x := by
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
  have hlow' : -((1/2)^16) ≤ (∑ i ∈ Finset.range 16, (1-x)^(i+1)/(i+1)) + Real.log x :=
    le_trans (neg_le_neg hb) hlow
  linarith


end TaoFivePrimes

open TaoFivePrimes

theorem solution (p : Nat) (hp : p ∈ pl521) :
    (llb p : Real) ≤ Real.log (Real.log (p : Real)) := by
  simp only [pl521, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ((clbZ 2 : Nat) : Real) ≤ Real.log ((2 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 2 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (2 : Nat) ∈ plist1))))
    have hser := le_log_taylor (6931/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 2 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (6931/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (0:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 2 = (-366597/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 2 : Real)/10^4) = Real.log (6931/10000 : Real) + 0 * Real.log 2 := by
      rw [show ((clbZ 2 : Real)/10^4) = (6931/10000 : Real) * (2:Real)^0 by
            rw [show clbZ 2 = 6931 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 2 : Real)/10^4) ≤ Real.log (Real.log ((2 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 2 = 6931 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (0:Real) * (6931471803/10000000000 : Real) ≤ (0:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 2 : Real) ≤ Real.log (6931/10000 : Real) + (0:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 3 : Nat) : Real) ≤ Real.log ((3 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 3 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (3 : Nat) ∈ plist1))))
    have hser := le_log_taylor (5493/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 3 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (5493/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (0:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 3 = (94021/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 3 : Real)/10^4) = Real.log (5493/5000 : Real) + 0 * Real.log 2 := by
      rw [show ((clbZ 3 : Real)/10^4) = (5493/5000 : Real) * (2:Real)^0 by
            rw [show clbZ 3 = 10986 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 3 : Real)/10^4) ≤ Real.log (Real.log ((3 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 3 = 10986 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (0:Real) * (6931471803/10000000000 : Real) ≤ (0:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 3 : Real) ≤ Real.log (5493/5000 : Real) + (0:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 5 : Nat) : Real) ≤ Real.log ((5 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 5 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (5 : Nat) ∈ plist1))))
    have hser := le_log_taylor (8047/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 5 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (8047/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 5 = (237923/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 5 : Real)/10^4) = Real.log (8047/10000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 5 : Real)/10^4) = (8047/10000 : Real) * (2:Real)^1 by
            rw [show clbZ 5 = 16094 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 5 : Real)/10^4) ≤ Real.log (Real.log ((5 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 5 = 16094 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 5 : Real) ≤ Real.log (8047/10000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 7 : Nat) : Real) ≤ Real.log ((7 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 7 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (7 : Nat) ∈ plist1))))
    have hser := le_log_taylor (19459/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 7 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (19459/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 7 = (665709/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 7 : Real)/10^4) = Real.log (19459/20000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 7 : Real)/10^4) = (19459/20000 : Real) * (2:Real)^1 by
            rw [show clbZ 7 = 19459 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 7 : Real)/10^4) ≤ Real.log (Real.log ((7 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 7 = 19459 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 7 : Real) ≤ Real.log (19459/20000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 11 : Nat) : Real) ≤ Real.log ((11 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 11 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (11 : Nat) ∈ plist1))))
    have hser := le_log_taylor (11989/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 11 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (11989/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 11 = (109317/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 11 : Real)/10^4) = Real.log (11989/10000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 11 : Real)/10^4) = (11989/10000 : Real) * (2:Real)^1 by
            rw [show clbZ 11 = 23978 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 11 : Real)/10^4) ≤ Real.log (Real.log ((11 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 11 = 23978 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 11 : Real) ≤ Real.log (11989/10000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 13 : Nat) : Real) ≤ Real.log ((13 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 13 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (13 : Nat) ∈ plist1))))
    have hser := le_log_taylor (25649/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 13 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (25649/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 13 = (58869/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 13 : Real)/10^4) = Real.log (25649/20000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 13 : Real)/10^4) = (25649/20000 : Real) * (2:Real)^1 by
            rw [show clbZ 13 = 25649 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 13 : Real)/10^4) ≤ Real.log (Real.log ((13 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 13 = 25649 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 13 : Real) ≤ Real.log (25649/20000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 17 : Nat) : Real) ≤ Real.log ((17 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 17 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (17 : Nat) ∈ plist1))))
    have hser := le_log_taylor (7083/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 17 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (7083/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 17 = (1041391/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 17 : Real)/10^4) = Real.log (7083/5000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 17 : Real)/10^4) = (7083/5000 : Real) * (2:Real)^1 by
            rw [show clbZ 17 = 28332 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 17 : Real)/10^4) ≤ Real.log (Real.log ((17 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 17 = 28332 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 17 : Real) ≤ Real.log (7083/5000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 19 : Nat) : Real) ≤ Real.log ((19 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 19 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (19 : Nat) ∈ plist1))))
    have hser := le_log_taylor (7361/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 19 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (7361/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (1:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 19 = (1079889/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 19 : Real)/10^4) = Real.log (7361/5000 : Real) + 1 * Real.log 2 := by
      rw [show ((clbZ 19 : Real)/10^4) = (7361/5000 : Real) * (2:Real)^1 by
            rw [show clbZ 19 = 29444 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 19 : Real)/10^4) ≤ Real.log (Real.log ((19 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 19 = 29444 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (1:Real) * (6931471803/10000000000 : Real) ≤ (1:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 19 : Real) ≤ Real.log (7361/5000 : Real) + (1:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 23 : Nat) : Real) ≤ Real.log ((23 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 23 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (23 : Nat) ∈ plist1))))
    have hser := le_log_taylor (15677/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 23 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (15677/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 23 = (1142741/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 23 : Real)/10^4) = Real.log (15677/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 23 : Real)/10^4) = (15677/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 23 = 31354 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 23 : Real)/10^4) ≤ Real.log (Real.log ((23 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 23 = 31354 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 23 : Real) ≤ Real.log (15677/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 29 : Nat) : Real) ≤ Real.log ((29 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 29 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (29 : Nat) ∈ plist1))))
    have hser := le_log_taylor (4209/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 29 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (4209/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 29 = (607033/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 29 : Real)/10^4) = Real.log (4209/5000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 29 : Real)/10^4) = (4209/5000 : Real) * (2:Real)^2 by
            rw [show clbZ 29 = 33672 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 29 : Real)/10^4) ≤ Real.log (Real.log ((29 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 29 = 33672 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 29 : Real) ≤ Real.log (4209/5000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 31 : Nat) : Real) ≤ Real.log ((31 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 31 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (31 : Nat) ∈ plist1))))
    have hser := le_log_taylor (34339/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 31 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (34339/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 31 = (1233681/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 31 : Real)/10^4) = Real.log (34339/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 31 : Real)/10^4) = (34339/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 31 = 34339 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 31 : Real)/10^4) ≤ Real.log (Real.log ((31 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 31 = 34339 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 31 : Real) ≤ Real.log (34339/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 37 : Nat) : Real) ≤ Real.log ((37 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 37 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (37 : Nat) ∈ plist1))))
    have hser := le_log_taylor (36109/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 37 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (36109/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 37 = (1283941/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 37 : Real)/10^4) = Real.log (36109/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 37 : Real)/10^4) = (36109/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 37 = 36109 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 37 : Real)/10^4) ≤ Real.log (Real.log ((37 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 37 = 36109 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 37 : Real) ≤ Real.log (36109/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 41 : Nat) : Real) ≤ Real.log ((41 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 41 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (41 : Nat) ∈ plist1))))
    have hser := le_log_taylor (7427/8000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 41 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (7427/8000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 41 = (1311959/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 41 : Real)/10^4) = Real.log (7427/8000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 41 : Real)/10^4) = (7427/8000 : Real) * (2:Real)^2 by
            rw [show clbZ 41 = 37135 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 41 : Real)/10^4) ≤ Real.log (Real.log ((41 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 41 = 37135 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 41 : Real) ≤ Real.log (7427/8000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 43 : Nat) : Real) ≤ Real.log ((43 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 43 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (43 : Nat) ∈ plist1))))
    have hser := le_log_taylor (9403/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 43 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (9403/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 43 = (662361/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 43 : Real)/10^4) = Real.log (9403/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 43 : Real)/10^4) = (9403/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 43 = 37612 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 43 : Real)/10^4) ≤ Real.log (Real.log ((43 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 43 = 37612 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 43 : Real) ≤ Real.log (9403/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 47 : Nat) : Real) ≤ Real.log ((47 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 47 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (47 : Nat) ∈ plist1))))
    have hser := le_log_taylor (38501/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 47 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (38501/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 47 = (1348083/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 47 : Real)/10^4) = Real.log (38501/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 47 : Real)/10^4) = (38501/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 47 = 38501 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 47 : Real)/10^4) ≤ Real.log (Real.log ((47 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 47 = 38501 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 47 : Real) ≤ Real.log (38501/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 53 : Nat) : Real) ≤ Real.log ((53 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 53 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (53 : Nat) ∈ plist1))))
    have hser := le_log_taylor (19851/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 53 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (19851/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 53 = (1378801/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 53 : Real)/10^4) = Real.log (19851/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 53 : Real)/10^4) = (19851/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 53 = 39702 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 53 : Real)/10^4) ≤ Real.log (Real.log ((53 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 53 = 39702 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 53 : Real) ≤ Real.log (19851/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 59 : Nat) : Real) ≤ Real.log ((59 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 59 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (59 : Nat) ∈ plist1))))
    have hser := le_log_taylor (1631/1600 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 59 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (1631/1600 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 59 = (351367/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 59 : Real)/10^4) = Real.log (1631/1600 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 59 : Real)/10^4) = (1631/1600 : Real) * (2:Real)^2 by
            rw [show clbZ 59 = 40775 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 59 : Real)/10^4) ≤ Real.log (Real.log ((59 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 59 = 40775 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 59 : Real) ≤ Real.log (1631/1600 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 61 : Nat) : Real) ≤ Real.log ((61 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 61 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (61 : Nat) ∈ plist1))))
    have hser := le_log_taylor (10277/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 61 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (10277/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 61 = (706801/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 61 : Real)/10^4) = Real.log (10277/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 61 : Real)/10^4) = (10277/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 61 = 41108 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 61 : Real)/10^4) ≤ Real.log (Real.log ((61 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 61 = 41108 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 61 : Real) ≤ Real.log (10277/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 67 : Nat) : Real) ≤ Real.log ((67 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 67 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (67 : Nat) ∈ plist1))))
    have hser := le_log_taylor (21023/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 67 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (21023/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 67 = (1436163/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 67 : Real)/10^4) = Real.log (21023/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 67 : Real)/10^4) = (21023/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 67 = 42046 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 67 : Real)/10^4) ≤ Real.log (Real.log ((67 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 67 = 42046 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 67 : Real) ≤ Real.log (21023/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 71 : Nat) : Real) ≤ Real.log ((71 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 71 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (71 : Nat) ∈ plist1))))
    have hser := le_log_taylor (21313/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 71 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (21313/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 71 = (181233/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 71 : Real)/10^4) = Real.log (21313/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 71 : Real)/10^4) = (21313/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 71 = 42626 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 71 : Real)/10^4) ≤ Real.log (Real.log ((71 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 71 = 42626 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 71 : Real) ≤ Real.log (21313/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 73 : Nat) : Real) ≤ Real.log ((73 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 73 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (73 : Nat) ∈ plist1))))
    have hser := le_log_taylor (5363/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 73 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (5363/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 73 = (364091/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 73 : Real)/10^4) = Real.log (5363/5000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 73 : Real)/10^4) = (5363/5000 : Real) * (2:Real)^2 by
            rw [show clbZ 73 = 42904 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 73 : Real)/10^4) ≤ Real.log (Real.log ((73 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 73 = 42904 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 73 : Real) ≤ Real.log (5363/5000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 79 : Nat) : Real) ≤ Real.log ((79 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 79 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (79 : Nat) ∈ plist1))))
    have hser := le_log_taylor (21847/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 79 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (21847/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 79 = (147461/100000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 79 : Real)/10^4) = Real.log (21847/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 79 : Real)/10^4) = (21847/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 79 = 43694 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 79 : Real)/10^4) ≤ Real.log (Real.log ((79 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 79 = 43694 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 79 : Real) ≤ Real.log (21847/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 83 : Nat) : Real) ≤ Real.log ((83 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 83 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (83 : Nat) ∈ plist1))))
    have hser := le_log_taylor (11047/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 83 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (11047/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 83 = (371463/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 83 : Real)/10^4) = Real.log (11047/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 83 : Real)/10^4) = (11047/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 83 = 44188 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 83 : Real)/10^4) ≤ Real.log (Real.log ((83 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 83 = 44188 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 83 : Real) ≤ Real.log (11047/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 89 : Nat) : Real) ≤ Real.log ((89 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 89 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (89 : Nat) ∈ plist1))))
    have hser := le_log_taylor (22443/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 89 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (22443/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 89 = (60061/40000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 89 : Real)/10^4) = Real.log (22443/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 89 : Real)/10^4) = (22443/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 89 = 44886 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 89 : Real)/10^4) ≤ Real.log (Real.log ((89 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 89 = 44886 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 89 : Real) ≤ Real.log (22443/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 97 : Nat) : Real) ≤ Real.log ((97 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 97 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (97 : Nat) ∈ plist1))))
    have hser := le_log_taylor (45747/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 97 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (45747/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 97 = (60821/40000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 97 : Real)/10^4) = Real.log (45747/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 97 : Real)/10^4) = (45747/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 97 = 45747 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 97 : Real)/10^4) ≤ Real.log (Real.log ((97 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 97 = 45747 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 97 : Real) ≤ Real.log (45747/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 101 : Nat) : Real) ≤ Real.log ((101 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 101 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (101 : Nat) ∈ plist1))))
    have hser := le_log_taylor (46151/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 101 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (46151/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 101 = (764659/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 101 : Real)/10^4) = Real.log (46151/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 101 : Real)/10^4) = (46151/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 101 = 46151 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 101 : Real)/10^4) ≤ Real.log (Real.log ((101 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 101 = 46151 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 101 : Real) ≤ Real.log (46151/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 103 : Nat) : Real) ≤ Real.log ((103 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 103 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (103 : Nat) ∈ plist1))))
    have hser := le_log_taylor (46347/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 103 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (46347/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 103 = (383389/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 103 : Real)/10^4) = Real.log (46347/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 103 : Real)/10^4) = (46347/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 103 = 46347 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 103 : Real)/10^4) ≤ Real.log (Real.log ((103 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 103 = 46347 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 103 : Real) ≤ Real.log (46347/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 107 : Nat) : Real) ≤ Real.log ((107 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 107 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (107 : Nat) ∈ plist1))))
    have hser := le_log_taylor (5841/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 107 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (5841/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 107 = (1541743/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 107 : Real)/10^4) = Real.log (5841/5000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 107 : Real)/10^4) = (5841/5000 : Real) * (2:Real)^2 by
            rw [show clbZ 107 = 46728 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 107 : Real)/10^4) ≤ Real.log (Real.log ((107 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 107 = 46728 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 107 : Real) ≤ Real.log (5841/5000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 109 : Nat) : Real) ≤ Real.log ((109 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 109 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (109 : Nat) ∈ plist1))))
    have hser := le_log_taylor (46913/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 109 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (46913/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 109 = (772847/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 109 : Real)/10^4) = Real.log (46913/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 109 : Real)/10^4) = (46913/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 109 = 46913 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 109 : Real)/10^4) ≤ Real.log (Real.log ((109 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 109 = 46913 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 109 : Real) ≤ Real.log (46913/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 113 : Nat) : Real) ≤ Real.log ((113 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 113 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (113 : Nat) ∈ plist1))))
    have hser := le_log_taylor (47273/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 113 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (47273/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 113 = (776669/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 113 : Real)/10^4) = Real.log (47273/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 113 : Real)/10^4) = (47273/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 113 = 47273 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 113 : Real)/10^4) ≤ Real.log (Real.log ((113 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 113 = 47273 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 113 : Real) ≤ Real.log (47273/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 127 : Nat) : Real) ≤ Real.log ((127 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 127 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (127 : Nat) ∈ plist1))))
    have hser := le_log_taylor (48441/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 127 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (48441/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 127 = (788873/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 127 : Real)/10^4) = Real.log (48441/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 127 : Real)/10^4) = (48441/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 127 = 48441 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 127 : Real)/10^4) ≤ Real.log (Real.log ((127 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 127 = 48441 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 127 : Real) ≤ Real.log (48441/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 131 : Nat) : Real) ≤ Real.log ((131 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 131 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (131 : Nat) ∈ plist1))))
    have hser := le_log_taylor (48751/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 131 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (48751/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 131 = (12673/8000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 131 : Real)/10^4) = Real.log (48751/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 131 : Real)/10^4) = (48751/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 131 = 48751 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 131 : Real)/10^4) ≤ Real.log (Real.log ((131 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 131 = 48751 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 131 : Real) ≤ Real.log (48751/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 137 : Nat) : Real) ≤ Real.log ((137 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 137 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (137 : Nat) ∈ plist1))))
    have hser := le_log_taylor (49199/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 137 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (49199/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 137 = (199159/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 137 : Real)/10^4) = Real.log (49199/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 137 : Real)/10^4) = (49199/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 137 = 49199 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 137 : Real)/10^4) ≤ Real.log (Real.log ((137 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 137 = 49199 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 137 : Real) ≤ Real.log (49199/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 139 : Nat) : Real) ≤ Real.log ((139 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 139 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (139 : Nat) ∈ plist1))))
    have hser := le_log_taylor (771/625 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 139 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (771/625 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 139 = (319243/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 139 : Real)/10^4) = Real.log (771/625 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 139 : Real)/10^4) = (771/625 : Real) * (2:Real)^2 by
            rw [show clbZ 139 = 49344 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 139 : Real)/10^4) ≤ Real.log (Real.log ((139 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 139 = 49344 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 139 : Real) ≤ Real.log (771/625 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 149 : Nat) : Real) ≤ Real.log ((149 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 149 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (149 : Nat) ∈ plist1))))
    have hser := le_log_taylor (50039/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 149 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (50039/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 149 = (805101/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 149 : Real)/10^4) = Real.log (50039/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 149 : Real)/10^4) = (50039/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 149 = 50039 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 149 : Real)/10^4) ≤ Real.log (Real.log ((149 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 149 = 50039 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 149 : Real) ≤ Real.log (50039/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 151 : Nat) : Real) ≤ Real.log ((151 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 151 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (151 : Nat) ∈ plist1))))
    have hser := le_log_taylor (12543/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 151 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (12543/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 151 = (201607/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 151 : Real)/10^4) = Real.log (12543/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 151 : Real)/10^4) = (12543/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 151 = 50172 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 151 : Real)/10^4) ≤ Real.log (Real.log ((151 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 151 = 50172 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 151 : Real) ≤ Real.log (12543/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 157 : Nat) : Real) ≤ Real.log ((157 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 157 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (157 : Nat) ∈ plist1))))
    have hser := le_log_taylor (25281/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 157 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (25281/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 157 = (1620599/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 157 : Real)/10^4) = Real.log (25281/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 157 : Real)/10^4) = (25281/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 157 = 50562 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 157 : Real)/10^4) ≤ Real.log (Real.log ((157 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 157 = 50562 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 157 : Real) ≤ Real.log (25281/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 163 : Nat) : Real) ≤ Real.log ((163 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 163 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (163 : Nat) ∈ plist1))))
    have hser := le_log_taylor (50937/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 163 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (50937/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 163 = (1627989/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 163 : Real)/10^4) = Real.log (50937/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 163 : Real)/10^4) = (50937/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 163 = 50937 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 163 : Real)/10^4) ≤ Real.log (Real.log ((163 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 163 = 50937 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 163 : Real) ≤ Real.log (50937/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 167 : Nat) : Real) ≤ Real.log ((167 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 167 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (167 : Nat) ∈ plist1))))
    have hser := le_log_taylor (51179/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 167 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (51179/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 167 = (204091/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 167 : Real)/10^4) = Real.log (51179/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 167 : Real)/10^4) = (51179/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 167 = 51179 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 167 : Real)/10^4) ≤ Real.log (Real.log ((167 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 167 = 51179 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 167 : Real) ≤ Real.log (51179/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 173 : Nat) : Real) ≤ Real.log ((173 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 173 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (173 : Nat) ∈ plist1))))
    have hser := le_log_taylor (12883/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 173 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (12883/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 173 = (819801/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 173 : Real)/10^4) = Real.log (12883/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 173 : Real)/10^4) = (12883/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 173 = 51532 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 173 : Real)/10^4) ≤ Real.log (Real.log ((173 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 173 = 51532 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 173 : Real) ≤ Real.log (12883/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 179 : Nat) : Real) ≤ Real.log ((179 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 179 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (179 : Nat) ∈ plist1))))
    have hser := le_log_taylor (51873/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 179 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (51873/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 179 = (823099/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 179 : Real)/10^4) = Real.log (51873/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 179 : Real)/10^4) = (51873/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 179 = 51873 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 179 : Real)/10^4) ≤ Real.log (Real.log ((179 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 179 = 51873 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 179 : Real) ≤ Real.log (51873/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 181 : Nat) : Real) ≤ Real.log ((181 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 181 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (181 : Nat) ∈ plist1))))
    have hser := le_log_taylor (3249/2500 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 181 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (3249/2500 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 181 = (329667/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 181 : Real)/10^4) = Real.log (3249/2500 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 181 : Real)/10^4) = (3249/2500 : Real) * (2:Real)^2 by
            rw [show clbZ 181 = 51984 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 181 : Real)/10^4) ≤ Real.log (Real.log ((181 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 181 = 51984 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 181 : Real) ≤ Real.log (3249/2500 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 191 : Nat) : Real) ≤ Real.log ((191 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 191 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (191 : Nat) ∈ plist1))))
    have hser := le_log_taylor (26261/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 191 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (26261/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 191 = (1658631/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 191 : Real)/10^4) = Real.log (26261/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 191 : Real)/10^4) = (26261/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 191 = 52522 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 191 : Real)/10^4) ≤ Real.log (Real.log ((191 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 191 = 52522 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 191 : Real) ≤ Real.log (26261/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 193 : Nat) : Real) ≤ Real.log ((193 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 193 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (193 : Nat) ∈ plist1))))
    have hser := le_log_taylor (26313/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 193 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (26313/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 193 = (1660609/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 193 : Real)/10^4) = Real.log (26313/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 193 : Real)/10^4) = (26313/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 193 = 52626 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 193 : Real)/10^4) ≤ Real.log (Real.log ((193 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 193 = 52626 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 193 : Real) ≤ Real.log (26313/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 197 : Nat) : Real) ≤ Real.log ((197 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 197 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (197 : Nat) ∈ plist1))))
    have hser := le_log_taylor (1651/1250 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 197 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (1651/1250 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 197 = (416129/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 197 : Real)/10^4) = Real.log (1651/1250 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 197 : Real)/10^4) = (1651/1250 : Real) * (2:Real)^2 by
            rw [show clbZ 197 = 52832 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 197 : Real)/10^4) ≤ Real.log (Real.log ((197 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 197 = 52832 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 197 : Real) ≤ Real.log (1651/1250 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 199 : Nat) : Real) ≤ Real.log ((199 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 199 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (199 : Nat) ∈ plist1))))
    have hser := le_log_taylor (52933/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 199 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (52933/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 199 = (833213/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 199 : Real)/10^4) = Real.log (52933/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 199 : Real)/10^4) = (52933/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 199 = 52933 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 199 : Real)/10^4) ≤ Real.log (Real.log ((199 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 199 = 52933 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 199 : Real) ≤ Real.log (52933/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 211 : Nat) : Real) ≤ Real.log ((211 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 211 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (211 : Nat) ∈ plist1))))
    have hser := le_log_taylor (26759/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 211 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (26759/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 211 = (1677417/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 211 : Real)/10^4) = Real.log (26759/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 211 : Real)/10^4) = (26759/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 211 = 53518 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 211 : Real)/10^4) ≤ Real.log (Real.log ((211 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 211 = 53518 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 211 : Real) ≤ Real.log (26759/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 223 : Nat) : Real) ≤ Real.log ((223 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 223 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (223 : Nat) ∈ plist1))))
    have hser := le_log_taylor (54071/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 223 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (54071/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 223 = (1687697/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 223 : Real)/10^4) = Real.log (54071/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 223 : Real)/10^4) = (54071/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 223 = 54071 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 223 : Real)/10^4) ≤ Real.log (Real.log ((223 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 223 = 54071 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 223 : Real) ≤ Real.log (54071/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 227 : Nat) : Real) ≤ Real.log ((227 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 227 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (227 : Nat) ∈ plist1))))
    have hser := le_log_taylor (54249/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 227 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (54249/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 227 = (211373/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 227 : Real)/10^4) = Real.log (54249/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 227 : Real)/10^4) = (54249/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 227 = 54249 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 227 : Real)/10^4) ≤ Real.log (Real.log ((227 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 227 = 54249 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 227 : Real) ≤ Real.log (54249/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 229 : Nat) : Real) ≤ Real.log ((229 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 229 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (229 : Nat) ∈ plist1))))
    have hser := le_log_taylor (54337/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 229 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (54337/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 229 = (338521/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 229 : Real)/10^4) = Real.log (54337/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 229 : Real)/10^4) = (54337/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 229 = 54337 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 229 : Real)/10^4) ≤ Real.log (Real.log ((229 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 229 = 54337 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 229 : Real) ≤ Real.log (54337/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 233 : Nat) : Real) ≤ Real.log ((233 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 233 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (233 : Nat) ∈ plist1))))
    have hser := le_log_taylor (5451/4000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 233 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (5451/4000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 233 = (1695783/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 233 : Real)/10^4) = Real.log (5451/4000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 233 : Real)/10^4) = (5451/4000 : Real) * (2:Real)^2 by
            rw [show clbZ 233 = 54510 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 233 : Real)/10^4) ≤ Real.log (Real.log ((233 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 233 = 54510 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 233 : Real) ≤ Real.log (5451/4000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 239 : Nat) : Real) ≤ Real.log ((239 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 239 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (239 : Nat) ∈ plist1))))
    have hser := le_log_taylor (13691/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 239 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (13691/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 239 = (106277/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 239 : Real)/10^4) = Real.log (13691/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 239 : Real)/10^4) = (13691/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 239 = 54764 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 239 : Real)/10^4) ≤ Real.log (Real.log ((239 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 239 = 54764 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 239 : Real) ≤ Real.log (13691/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 241 : Nat) : Real) ≤ Real.log ((241 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 241 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (241 : Nat) ∈ plist1))))
    have hser := le_log_taylor (54847/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 241 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (54847/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 241 = (1701947/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 241 : Real)/10^4) = Real.log (54847/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 241 : Real)/10^4) = (54847/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 241 = 54847 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 241 : Real)/10^4) ≤ Real.log (Real.log ((241 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 241 = 54847 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 241 : Real) ≤ Real.log (54847/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 251 : Nat) : Real) ≤ Real.log ((251 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 251 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (251 : Nat) ∈ plist1))))
    have hser := le_log_taylor (27627/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 251 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (27627/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 251 = (85467/50000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 251 : Real)/10^4) = Real.log (27627/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 251 : Real)/10^4) = (27627/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 251 = 55254 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 251 : Real)/10^4) ≤ Real.log (Real.log ((251 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 251 = 55254 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 251 : Real) ≤ Real.log (27627/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 257 : Nat) : Real) ≤ Real.log ((257 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 257 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (by decide : (257 : Nat) ∈ plist1))))
    have hser := le_log_taylor (5549/4000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 257 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (5549/4000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 257 = (856801/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 257 : Real)/10^4) = Real.log (5549/4000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 257 : Real)/10^4) = (5549/4000 : Real) * (2:Real)^2 by
            rw [show clbZ 257 = 55490 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 257 : Real)/10^4) ≤ Real.log (Real.log ((257 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 257 = 55490 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 257 : Real) ≤ Real.log (5549/4000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 263 : Nat) : Real) ≤ Real.log ((263 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 263 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (263 : Nat) ∈ plist2))))
    have hser := le_log_taylor (55721/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 263 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (55721/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 263 = (429439/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 263 : Real)/10^4) = Real.log (55721/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 263 : Real)/10^4) = (55721/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 263 = 55721 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 263 : Real)/10^4) ≤ Real.log (Real.log ((263 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 263 = 55721 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 263 : Real) ≤ Real.log (55721/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 269 : Nat) : Real) ≤ Real.log ((269 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 269 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (269 : Nat) ∈ plist2))))
    have hser := le_log_taylor (55947/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 269 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (55947/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 269 = (430451/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 269 : Real)/10^4) = Real.log (55947/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 269 : Real)/10^4) = (55947/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 269 = 55947 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 269 : Real)/10^4) ≤ Real.log (Real.log ((269 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 269 = 55947 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 269 : Real) ≤ Real.log (55947/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 271 : Nat) : Real) ≤ Real.log ((271 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 271 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (271 : Nat) ∈ plist2))))
    have hser := le_log_taylor (56021/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 271 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (56021/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 271 = (861563/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 271 : Real)/10^4) = Real.log (56021/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 271 : Real)/10^4) = (56021/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 271 = 56021 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 271 : Real)/10^4) ≤ Real.log (Real.log ((271 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 271 = 56021 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 271 : Real) ≤ Real.log (56021/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 277 : Nat) : Real) ≤ Real.log ((277 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 277 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (277 : Nat) ∈ plist2))))
    have hser := le_log_taylor (703/500 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 277 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (703/500 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 277 = (1727027/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 277 : Real)/10^4) = Real.log (703/500 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 277 : Real)/10^4) = (703/500 : Real) * (2:Real)^2 by
            rw [show clbZ 277 = 56240 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 277 : Real)/10^4) ≤ Real.log (Real.log ((277 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 277 = 56240 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 277 : Real) ≤ Real.log (703/500 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 281 : Nat) : Real) ≤ Real.log ((281 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 281 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (281 : Nat) ∈ plist2))))
    have hser := le_log_taylor (56383/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 281 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (56383/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 281 = (1729567/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 281 : Real)/10^4) = Real.log (56383/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 281 : Real)/10^4) = (56383/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 281 = 56383 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 281 : Real)/10^4) ≤ Real.log (Real.log ((281 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 281 = 56383 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 281 : Real) ≤ Real.log (56383/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 283 : Nat) : Real) ≤ Real.log ((283 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 283 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (283 : Nat) ∈ plist2))))
    have hser := le_log_taylor (28227/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 283 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (28227/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 283 = (69233/40000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 283 : Real)/10^4) = Real.log (28227/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 283 : Real)/10^4) = (28227/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 283 = 56454 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 283 : Real)/10^4) ≤ Real.log (Real.log ((283 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 283 = 56454 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 283 : Real) ≤ Real.log (28227/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 293 : Nat) : Real) ≤ Real.log ((293 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 293 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (293 : Nat) ∈ plist2))))
    have hser := le_log_taylor (56801/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 293 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (56801/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 293 = (1736953/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 293 : Real)/10^4) = Real.log (56801/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 293 : Real)/10^4) = (56801/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 293 = 56801 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 293 : Real)/10^4) ≤ Real.log (Real.log ((293 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 293 = 56801 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 293 : Real) ≤ Real.log (56801/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 307 : Nat) : Real) ≤ Real.log ((307 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 307 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (307 : Nat) ∈ plist2))))
    have hser := le_log_taylor (14317/10000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 307 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (14317/10000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 307 = (1745141/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 307 : Real)/10^4) = Real.log (14317/10000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 307 : Real)/10^4) = (14317/10000 : Real) * (2:Real)^2 by
            rw [show clbZ 307 = 57268 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 307 : Real)/10^4) ≤ Real.log (Real.log ((307 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 307 = 57268 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 307 : Real) ≤ Real.log (14317/10000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 311 : Nat) : Real) ≤ Real.log ((311 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 311 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (311 : Nat) ∈ plist2))))
    have hser := le_log_taylor (57397/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 311 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (57397/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 311 = (1747391/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 311 : Real)/10^4) = Real.log (57397/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 311 : Real)/10^4) = (57397/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 311 = 57397 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 311 : Real)/10^4) ≤ Real.log (Real.log ((311 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 311 = 57397 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 311 : Real) ≤ Real.log (57397/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 313 : Nat) : Real) ≤ Real.log ((313 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 313 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (313 : Nat) ∈ plist2))))
    have hser := le_log_taylor (28731/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 313 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (28731/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 313 = (1748523/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 313 : Real)/10^4) = Real.log (28731/20000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 313 : Real)/10^4) = (28731/20000 : Real) * (2:Real)^2 by
            rw [show clbZ 313 = 57462 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 313 : Real)/10^4) ≤ Real.log (Real.log ((313 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 313 = 57462 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 313 : Real) ≤ Real.log (28731/20000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 317 : Nat) : Real) ≤ Real.log ((317 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 317 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (317 : Nat) ∈ plist2))))
    have hser := le_log_taylor (57589/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 317 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (57589/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 317 = (1750731/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 317 : Real)/10^4) = Real.log (57589/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 317 : Real)/10^4) = (57589/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 317 = 57589 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 317 : Real)/10^4) ≤ Real.log (Real.log ((317 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 317 = 57589 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 317 : Real) ≤ Real.log (57589/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 331 : Nat) : Real) ≤ Real.log ((331 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 331 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (331 : Nat) ∈ plist2))))
    have hser := le_log_taylor (58021/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 331 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (58021/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 331 = (439551/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 331 : Real)/10^4) = Real.log (58021/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 331 : Real)/10^4) = (58021/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 331 = 58021 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 331 : Real)/10^4) ≤ Real.log (Real.log ((331 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 331 = 58021 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 331 : Real) ≤ Real.log (58021/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 337 : Nat) : Real) ≤ Real.log ((337 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 337 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (337 : Nat) ∈ plist2))))
    have hser := le_log_taylor (291/200 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 337 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (291/200 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 337 = (440321/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 337 : Real)/10^4) = Real.log (291/200 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 337 : Real)/10^4) = (291/200 : Real) * (2:Real)^2 by
            rw [show clbZ 337 = 58200 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 337 : Real)/10^4) ≤ Real.log (Real.log ((337 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 337 = 58200 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 337 : Real) ≤ Real.log (291/200 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 347 : Nat) : Real) ≤ Real.log ((347 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 347 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (347 : Nat) ∈ plist2))))
    have hser := le_log_taylor (58493/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 347 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (58493/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 347 = (883153/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 347 : Real)/10^4) = Real.log (58493/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 347 : Real)/10^4) = (58493/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 347 = 58493 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 347 : Real)/10^4) ≤ Real.log (Real.log ((347 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 347 = 58493 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 347 : Real) ≤ Real.log (58493/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 349 : Nat) : Real) ≤ Real.log ((349 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 349 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (349 : Nat) ∈ plist2))))
    have hser := le_log_taylor (1171/800 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 349 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (1171/800 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 349 = (22091/12500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 349 : Real)/10^4) = Real.log (1171/800 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 349 : Real)/10^4) = (1171/800 : Real) * (2:Real)^2 by
            rw [show clbZ 349 = 58550 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 349 : Real)/10^4) ≤ Real.log (Real.log ((349 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 349 = 58550 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 349 : Real) ≤ Real.log (1171/800 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 353 : Nat) : Real) ≤ Real.log ((353 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 353 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (353 : Nat) ∈ plist2))))
    have hser := le_log_taylor (7333/5000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 353 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (7333/5000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 353 = (70769/40000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 353 : Real)/10^4) = Real.log (7333/5000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 353 : Real)/10^4) = (7333/5000 : Real) * (2:Real)^2 by
            rw [show clbZ 353 = 58664 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 353 : Real)/10^4) ≤ Real.log (Real.log ((353 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 353 = 58664 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 353 : Real) ≤ Real.log (7333/5000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 359 : Nat) : Real) ≤ Real.log ((359 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 359 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (359 : Nat) ∈ plist2))))
    have hser := le_log_taylor (58833/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 359 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (58833/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 359 = (886051/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 359 : Real)/10^4) = Real.log (58833/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 359 : Real)/10^4) = (58833/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 359 = 58833 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 359 : Real)/10^4) ≤ Real.log (Real.log ((359 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 359 = 58833 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 359 : Real) ≤ Real.log (58833/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 367 : Nat) : Real) ≤ Real.log ((367 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 367 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (367 : Nat) ∈ plist2))))
    have hser := le_log_taylor (59053/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 367 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (59053/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 367 = (887917/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 367 : Real)/10^4) = Real.log (59053/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 367 : Real)/10^4) = (59053/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 367 = 59053 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 367 : Real)/10^4) ≤ Real.log (Real.log ((367 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 367 = 59053 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 367 : Real) ≤ Real.log (59053/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 373 : Nat) : Real) ≤ Real.log ((373 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 373 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (373 : Nat) ∈ plist2))))
    have hser := le_log_taylor (11843/8000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 373 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (11843/8000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 373 = (889287/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 373 : Real)/10^4) = Real.log (11843/8000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 373 : Real)/10^4) = (11843/8000 : Real) * (2:Real)^2 by
            rw [show clbZ 373 = 59215 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 373 : Real)/10^4) ≤ Real.log (Real.log ((373 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 373 = 59215 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 373 : Real) ≤ Real.log (11843/8000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 379 : Nat) : Real) ≤ Real.log ((379 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 379 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (379 : Nat) ∈ plist2))))
    have hser := le_log_taylor (95/64 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 379 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (95/64 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 379 = (222659/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 379 : Real)/10^4) = Real.log (95/64 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 379 : Real)/10^4) = (95/64 : Real) * (2:Real)^2 by
            rw [show clbZ 379 = 59375 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 379 : Real)/10^4) ≤ Real.log (Real.log ((379 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 379 = 59375 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 379 : Real) ≤ Real.log (95/64 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 383 : Nat) : Real) ≤ Real.log ((383 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 383 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (383 : Nat) ∈ plist2))))
    have hser := le_log_taylor (1487/1000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 383 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (1487/1000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 383 = (1783039/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 383 : Real)/10^4) = Real.log (1487/1000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 383 : Real)/10^4) = (1487/1000 : Real) * (2:Real)^2 by
            rw [show clbZ 383 = 59480 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 383 : Real)/10^4) ≤ Real.log (Real.log ((383 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 383 = 59480 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 383 : Real) ≤ Real.log (1487/1000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 389 : Nat) : Real) ≤ Real.log ((389 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 389 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (389 : Nat) ∈ plist2))))
    have hser := le_log_taylor (11927/8000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 389 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (11927/8000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 389 = (892821/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 389 : Real)/10^4) = Real.log (11927/8000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 389 : Real)/10^4) = (11927/8000 : Real) * (2:Real)^2 by
            rw [show clbZ 389 = 59635 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 389 : Real)/10^4) ≤ Real.log (Real.log ((389 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 389 = 59635 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 389 : Real) ≤ Real.log (11927/8000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 397 : Nat) : Real) ≤ Real.log ((397 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 397 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (397 : Nat) ∈ plist2))))
    have hser := le_log_taylor (59839/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 397 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (59839/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 397 = (1789057/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 397 : Real)/10^4) = Real.log (59839/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 397 : Real)/10^4) = (59839/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 397 = 59839 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 397 : Real)/10^4) ≤ Real.log (Real.log ((397 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 397 = 59839 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 397 : Real) ≤ Real.log (59839/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 401 : Nat) : Real) ≤ Real.log ((401 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 401 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (401 : Nat) ∈ plist2))))
    have hser := le_log_taylor (59939/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 401 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (59939/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (2:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 401 = (895363/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 401 : Real)/10^4) = Real.log (59939/40000 : Real) + 2 * Real.log 2 := by
      rw [show ((clbZ 401 : Real)/10^4) = (59939/40000 : Real) * (2:Real)^2 by
            rw [show clbZ 401 = 59939 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 401 : Real)/10^4) ≤ Real.log (Real.log ((401 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 401 = 59939 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (2:Real) * (6931471803/10000000000 : Real) ≤ (2:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 401 : Real) ≤ Real.log (59939/40000 : Real) + (2:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 409 : Nat) : Real) ≤ Real.log ((409 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 409 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (409 : Nat) ∈ plist2))))
    have hser := le_log_taylor (60137/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 409 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (60137/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 409 = (224253/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 409 : Real)/10^4) = Real.log (60137/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 409 : Real)/10^4) = (60137/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 409 = 60137 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 409 : Real)/10^4) ≤ Real.log (Real.log ((409 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 409 = 60137 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 409 : Real) ≤ Real.log (60137/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 419 : Nat) : Real) ≤ Real.log ((419 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 419 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (419 : Nat) ∈ plist2))))
    have hser := le_log_taylor (30189/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 419 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (30189/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 419 = (224753/125000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 419 : Real)/10^4) = Real.log (30189/40000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 419 : Real)/10^4) = (30189/40000 : Real) * (2:Real)^3 by
            rw [show clbZ 419 = 60378 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 419 : Real)/10^4) ≤ Real.log (Real.log ((419 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 419 = 60378 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 419 : Real) ≤ Real.log (30189/40000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 421 : Nat) : Real) ≤ Real.log ((421 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 421 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (421 : Nat) ∈ plist2))))
    have hser := le_log_taylor (30213/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 421 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (30213/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 421 = (1798819/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 421 : Real)/10^4) = Real.log (30213/40000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 421 : Real)/10^4) = (30213/40000 : Real) * (2:Real)^3 by
            rw [show clbZ 421 = 60426 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 421 : Real)/10^4) ≤ Real.log (Real.log ((421 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 421 = 60426 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 421 : Real) ≤ Real.log (30213/40000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 431 : Nat) : Real) ≤ Real.log ((431 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 431 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (431 : Nat) ∈ plist2))))
    have hser := le_log_taylor (60661/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 431 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (60661/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 431 = (18027/10000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 431 : Real)/10^4) = Real.log (60661/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 431 : Real)/10^4) = (60661/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 431 = 60661 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 431 : Real)/10^4) ≤ Real.log (Real.log ((431 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 431 = 60661 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 431 : Real) ≤ Real.log (60661/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 433 : Nat) : Real) ≤ Real.log ((433 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 433 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (433 : Nat) ∈ plist2))))
    have hser := le_log_taylor (60707/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 433 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (60707/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 433 = (901729/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 433 : Real)/10^4) = Real.log (60707/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 433 : Real)/10^4) = (60707/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 433 = 60707 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 433 : Real)/10^4) ≤ Real.log (Real.log ((433 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 433 = 60707 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 433 : Real) ≤ Real.log (60707/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 439 : Nat) : Real) ≤ Real.log ((439 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 439 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (439 : Nat) ∈ plist2))))
    have hser := le_log_taylor (15211/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 439 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (15211/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 439 = (112857/62500) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 439 : Real)/10^4) = Real.log (15211/20000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 439 : Real)/10^4) = (15211/20000 : Real) * (2:Real)^3 by
            rw [show clbZ 439 = 60844 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 439 : Real)/10^4) ≤ Real.log (Real.log ((439 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 439 = 60844 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 439 : Real) ≤ Real.log (15211/20000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 443 : Nat) : Real) ≤ Real.log ((443 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 443 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (443 : Nat) ∈ plist2))))
    have hser := le_log_taylor (12187/16000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 443 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (12187/16000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 443 = (1807207/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 443 : Real)/10^4) = Real.log (12187/16000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 443 : Real)/10^4) = (12187/16000 : Real) * (2:Real)^3 by
            rw [show clbZ 443 = 60935 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 443 : Real)/10^4) ≤ Real.log (Real.log ((443 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 443 = 60935 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 443 : Real) ≤ Real.log (12187/16000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 449 : Nat) : Real) ≤ Real.log ((449 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 449 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (449 : Nat) ∈ plist2))))
    have hser := le_log_taylor (6107/8000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 449 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (6107/8000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 449 = (90471/50000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 449 : Real)/10^4) = Real.log (6107/8000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 449 : Real)/10^4) = (6107/8000 : Real) * (2:Real)^3 by
            rw [show clbZ 449 = 61070 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 449 : Real)/10^4) ≤ Real.log (Real.log ((449 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 449 = 61070 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 449 : Real) ≤ Real.log (6107/8000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 457 : Nat) : Real) ≤ Real.log ((457 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 457 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (457 : Nat) ∈ plist2))))
    have hser := le_log_taylor (30623/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 457 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (30623/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 457 = (906149/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 457 : Real)/10^4) = Real.log (30623/40000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 457 : Real)/10^4) = (30623/40000 : Real) * (2:Real)^3 by
            rw [show clbZ 457 = 61246 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 457 : Real)/10^4) ≤ Real.log (Real.log ((457 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 457 = 61246 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 457 : Real) ≤ Real.log (30623/40000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 461 : Nat) : Real) ≤ Real.log ((461 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 461 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (461 : Nat) ∈ plist2))))
    have hser := le_log_taylor (61333/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 461 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (61333/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 461 = (1813717/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 461 : Real)/10^4) = Real.log (61333/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 461 : Real)/10^4) = (61333/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 461 = 61333 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 461 : Real)/10^4) ≤ Real.log (Real.log ((461 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 461 = 61333 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 461 : Real) ≤ Real.log (61333/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 463 : Nat) : Real) ≤ Real.log ((463 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 463 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (463 : Nat) ∈ plist2))))
    have hser := le_log_taylor (61377/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 463 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (61377/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 463 = (907217/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 463 : Real)/10^4) = Real.log (61377/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 463 : Real)/10^4) = (61377/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 463 = 61377 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 463 : Real)/10^4) ≤ Real.log (Real.log ((463 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 463 = 61377 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 463 : Real) ≤ Real.log (61377/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 467 : Nat) : Real) ≤ Real.log ((467 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 467 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (467 : Nat) ∈ plist2))))
    have hser := le_log_taylor (61463/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 467 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (61463/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 467 = (363167/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 467 : Real)/10^4) = Real.log (61463/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 467 : Real)/10^4) = (61463/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 467 = 61463 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 467 : Real)/10^4) ≤ Real.log (Real.log ((467 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 467 = 61463 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 467 : Real) ≤ Real.log (61463/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 479 : Nat) : Real) ≤ Real.log ((479 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 479 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (479 : Nat) ∈ plist2))))
    have hser := le_log_taylor (61717/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 479 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (61717/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 479 = (1819959/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 479 : Real)/10^4) = Real.log (61717/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 479 : Real)/10^4) = (61717/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 479 = 61717 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 479 : Real)/10^4) ≤ Real.log (Real.log ((479 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 479 = 61717 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 479 : Real) ≤ Real.log (61717/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 487 : Nat) : Real) ≤ Real.log ((487 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 487 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (487 : Nat) ∈ plist2))))
    have hser := le_log_taylor (30941/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 487 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (30941/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 487 = (455657/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 487 : Real)/10^4) = Real.log (30941/40000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 487 : Real)/10^4) = (30941/40000 : Real) * (2:Real)^3 by
            rw [show clbZ 487 = 61882 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 487 : Real)/10^4) ≤ Real.log (Real.log ((487 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 487 = 61882 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 487 : Real) ≤ Real.log (30941/40000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 491 : Nat) : Real) ≤ Real.log ((491 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 491 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (491 : Nat) ∈ plist2))))
    have hser := le_log_taylor (15491/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 491 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (15491/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 491 = (1823953/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 491 : Real)/10^4) = Real.log (15491/20000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 491 : Real)/10^4) = (15491/20000 : Real) * (2:Real)^3 by
            rw [show clbZ 491 = 61964 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 491 : Real)/10^4) ≤ Real.log (Real.log ((491 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 491 = 61964 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 491 : Real) ≤ Real.log (15491/20000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 499 : Nat) : Real) ≤ Real.log ((499 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 499 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (499 : Nat) ∈ plist2))))
    have hser := le_log_taylor (31063/40000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 499 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (31063/40000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 499 = (456641/250000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 499 : Real)/10^4) = Real.log (31063/40000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 499 : Real)/10^4) = (31063/40000 : Real) * (2:Real)^3 by
            rw [show clbZ 499 = 62126 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 499 : Real)/10^4) ≤ Real.log (Real.log ((499 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 499 = 62126 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 499 : Real) ≤ Real.log (31063/40000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 503 : Nat) : Real) ≤ Real.log ((503 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 503 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (503 : Nat) ∈ plist2))))
    have hser := le_log_taylor (12441/16000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 503 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (12441/16000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 503 = (365567/200000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 503 : Real)/10^4) = Real.log (12441/16000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 503 : Real)/10^4) = (12441/16000 : Real) * (2:Real)^3 by
            rw [show clbZ 503 = 62205 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 503 : Real)/10^4) ≤ Real.log (Real.log ((503 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 503 = 62205 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 503 : Real) ≤ Real.log (12441/16000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 509 : Nat) : Real) ≤ Real.log ((509 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 509 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (509 : Nat) ∈ plist2))))
    have hser := le_log_taylor (15581/20000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 509 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (15581/20000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 509 = (914873/500000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 509 : Real)/10^4) = Real.log (15581/20000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 509 : Real)/10^4) = (15581/20000 : Real) * (2:Real)^3 by
            rw [show clbZ 509 = 62324 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 509 : Real)/10^4) ≤ Real.log (Real.log ((509 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 509 = 62324 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 509 : Real) ≤ Real.log (15581/20000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle

  · have hc : ((clbZ 521 : Nat) : Real) ≤ Real.log ((521 : Nat) : Real) * 10^4 := theta_cert_clbZ_le_log 521 (by rw [plist, Finset.mem_union, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (by decide : (521 : Nat) ∈ plist2))))
    have hser := le_log_taylor (62557/80000 : Real) (by norm_num) (by norm_num)
    have hnum : (llb 521 : Real) ≤ -(∑ i ∈ Finset.range 16, (1 - (62557/80000 : Real))^(i+1)/(i+1)) - (1/2)^16 + (3:Real)*(6931471803/10000000000 : Real) := by
      norm_num [show llb 521 = (1833477/1000000) by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
    have hdec : Real.log ((clbZ 521 : Real)/10^4) = Real.log (62557/80000 : Real) + 3 * Real.log 2 := by
      rw [show ((clbZ 521 : Real)/10^4) = (62557/80000 : Real) * (2:Real)^3 by
            rw [show clbZ 521 = 62557 by rfl]; norm_num]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      ring
    have hle : Real.log ((clbZ 521 : Real)/10^4) ≤ Real.log (Real.log ((521 : Nat) : Real)) :=
      Real.log_le_log (by rw [show clbZ 521 = 62557 by rfl]; norm_num)
        (by rw [div_le_iff₀ (by norm_num : (0:Real) < 10^4)]; exact hc)
    rw [hdec] at hle
    have hlog2 : (6931471803/10000000000 : Real) < Real.log 2 := by
      have hl := Real.log_two_gt_d9
      norm_num at hl
      linarith
    have hmul : (3:Real) * (6931471803/10000000000 : Real) ≤ (3:Real) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by norm_num)
    have hfin : (llb 521 : Real) ≤ Real.log (62557/80000 : Real) + (3:Real) * Real.log 2 := by linarith
    exact le_trans hfin hle


