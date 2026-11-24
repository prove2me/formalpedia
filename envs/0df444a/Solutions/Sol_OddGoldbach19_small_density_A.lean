-- Prove2me | solution 1 for OddGoldbach19.small_density_A
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:11:53.564541+00:00
-- url     : https://prove2.me/submissions/d9a0bc60-87e7-48e3-99f0-fcd674a81e0f

import Theorems.Thm_OddGoldbach19_small_count_A
import Theorems.Thm_Schnir_pi_lower
import Definitions.Def_Schnir_defs
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic
import Mathlib

namespace OddGoldbach21
/-- Strong prime-counting input from the existing Rosser--Schoenfeld theorem. -/
theorem primeCounting_lower18 (n : ℕ) (hn : 1340 ≤ n) (hl : 18 ≤ Real.log n) :
    (0.972 : ℝ) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := by linarith
  have htheta := TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic (n : ℝ) (by exact_mod_cast hn)
  have hupper := Chebyshev.theta_le_pi_mul_log n
  have hinv : 1 / (2 * Real.log (n : ℝ)) ≤ (0.028 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  apply (div_le_iff₀ hlog).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith
end OddGoldbach21


namespace OddGoldbach21
/-- Strong prime-counting input from the existing Rosser--Schoenfeld theorem. -/
theorem primeCounting_lower11 (n : ℕ) (hn : 1340 ≤ n) (hl : 11 ≤ Real.log n) :
    (0.954 : ℝ) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := by linarith
  have htheta := TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic (n : ℝ) (by exact_mod_cast hn)
  have hupper := Chebyshev.theta_le_pi_mul_log n
  have hinv : 1 / (2 * Real.log (n : ℝ)) ≤ (0.046 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  apply (div_le_iff₀ hlog).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith
end OddGoldbach21


set_option autoImplicit false
open Finset Real
open scoped Pointwise
namespace OddGoldbach19

theorem small_mem_A (a : ℕ) (ha : 1 ≤ a) (hb : a ≤ 56) : a ∈ Schnir.A := by
  interval_cases a
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 1, ⟨5, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 4, ⟨11, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 5, ⟨13, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 5, ⟨13, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 7, ⟨17, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 8, ⟨19, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 8, ⟨19, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 10, ⟨23, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 10, ⟨23, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 10, ⟨23, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 13, ⟨29, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 14, ⟨31, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 14, ⟨31, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 14, ⟨31, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 17, ⟨37, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 17, ⟨37, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 19, ⟨41, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 20, ⟨43, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 20, ⟨43, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 22, ⟨47, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 22, ⟨47, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 22, ⟨47, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 25, ⟨53, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 25, ⟨53, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 25, ⟨53, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 28, ⟨59, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 29, ⟨61, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 29, ⟨61, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 29, ⟨61, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 32, ⟨67, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 32, ⟨67, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 34, ⟨71, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 35, ⟨73, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 35, ⟨73, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 35, ⟨73, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 38, ⟨79, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 38, ⟨79, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 40, ⟨83, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 40, ⟨83, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 40, ⟨83, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 43, ⟨89, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 43, ⟨89, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨2, ⟨7, by norm_num, by norm_num, rfl⟩, 43, ⟨89, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨8, ⟨19, by norm_num, by norm_num, rfl⟩, 38, ⟨79, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 47, ⟨97, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 47, ⟨97, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 49, ⟨101, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 50, ⟨103, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 50, ⟨103, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 52, ⟨107, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 53, ⟨109, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 53, ⟨109, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨0, ⟨3, by norm_num, by norm_num, rfl⟩, 55, ⟨113, by norm_num, by norm_num, rfl⟩, rfl⟩
  · exact Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 55, ⟨113, by norm_num, by norm_num, rfl⟩, rfl⟩

end OddGoldbach19
open OddGoldbach19
open Classical in
theorem solution (N : ℕ) (hN : 1 ≤ N)
    (hlog26 : Real.log ((2 * N + 6 : ℕ) : ℝ) ≤ 26) :
    (N : ℝ) / 9 ≤ (((Ioc 0 N).filter (fun a => a ∈ Schnir.A)).card : ℝ) := by
  classical
  let C := ((Ioc 0 N).filter (fun a => a ∈ Schnir.A)).card
  change (N : ℝ) / 9 ≤ (C : ℝ)
  by_cases hs : N < 500
  · by_cases h56 : N ≤ 56
    · have he : (Ioc 0 N).filter (fun a => a ∈ Schnir.A) = Ioc 0 N := by
        apply filter_eq_self.2
        intro a ha
        exact small_mem_A a (by have := mem_Ioc.1 ha; omega) (by have := mem_Ioc.1 ha; omega)
      have hc : C = N := by simp [C, he]
      rw [hc]
      have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    · have hsub : Icc 1 56 ⊆ (Ioc 0 N).filter (fun a => a ∈ Schnir.A) := by
        intro a ha
        have ha' := mem_Icc.1 ha
        exact mem_filter.2 ⟨mem_Ioc.2 ⟨by omega, by omega⟩, small_mem_A a ha'.1 ha'.2⟩
      have hc := card_le_card hsub
      norm_num at hc
      have hcR : (56 : ℝ) ≤ C := by exact_mod_cast hc
      have hnR : (N : ℝ) < 500 := by exact_mod_cast hs
      linarith
  have h500 : 500 ≤ N := by omega
  have hcount := small_count_A N (by omega)
  have hcountR : 3 * (Nat.primeCounting (2 * N + 1) : ℝ) ≤ 2 * (C : ℝ) + 12 := by
    exact_mod_cast hcount
  have hypos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hlogpos : 0 < log ((2 * N + 1 : ℕ) : ℝ) := log_pos (by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith)
  have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting (2 * N + 1) : ℝ) := Nat.cast_nonneg _
  by_cases hlo : N < 100000
  · have hl13 : log ((2 * N + 1 : ℕ) : ℝ) ≤ 13 := by
      apply (log_le_iff_le_exp hypos).2
      have he : exp 13 = exp 1 ^ 13 := by rw [← exp_nat_mul]; norm_num
      have hb : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) hb 13
      rw [← he] at hp
      have hnR : (N : ℝ) < 100000 := by exact_mod_cast hlo
      push_cast
      norm_num at hp
      linarith
    have hp := Schnir.pi_lower ((2 * N + 1 : ℕ) : ℝ)
      (by exact_mod_cast (show 1000 ≤ 2 * N + 1 by omega))
    simp only [Nat.floor_natCast] at hp
    have hp' := (div_le_iff₀ (show (0 : ℝ) < 3 * log ((2 * N + 1 : ℕ) : ℝ) by positivity)).1 hp
    have hm := mul_le_mul_of_nonneg_left hl13 hpi0
    have hnR : (500 : ℝ) ≤ N := by exact_mod_cast h500
    push_cast at hp' hm hlogpos
    nlinarith only [hp', hm, hcountR, hnR, hlogpos]
  have hlarge : 100000 ≤ N := by omega
  have hn1340 : 1340 ≤ 2 * N + 1 := by omega
  by_cases hm : N < 100000000
  · have hl11 : 11 ≤ log ((2 * N + 1 : ℕ) : ℝ) := by
      apply (le_log_iff_exp_le hypos).2
      have he : exp 11 = exp 1 ^ 11 := by rw [← exp_nat_mul]; norm_num
      have hp := pow_le_pow_left₀ (exp_pos 1).le (show exp 1 ≤ (3 : ℝ) by linarith [exp_one_lt_d9]) 11
      rw [← he] at hp
      have hnR : (100000 : ℝ) ≤ N := by exact_mod_cast hlarge
      push_cast
      norm_num at hp
      linarith
    have hl20 : log ((2 * N + 1 : ℕ) : ℝ) ≤ 20 := by
      apply (log_le_iff_le_exp hypos).2
      have he : exp 20 = exp 1 ^ 20 := by rw [← exp_nat_mul]; norm_num
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
        (show (2.7 : ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) 20
      rw [← he] at hp
      have hnR : (N : ℝ) < 100000000 := by exact_mod_cast hm
      push_cast
      norm_num at hp
      linarith
    have hp := OddGoldbach21.primeCounting_lower11 (2 * N + 1) hn1340 hl11
    have hp' := (div_le_iff₀ hlogpos).1 hp
    have hmul := mul_le_mul_of_nonneg_left hl20 hpi0
    have hnR : (100000 : ℝ) ≤ N := by exact_mod_cast hlarge
    push_cast at hp' hmul
    nlinarith only [hp', hmul, hcountR, hnR]
  · have hlarge8 : 100000000 ≤ N := by omega
    have hl18 : 18 ≤ log ((2 * N + 1 : ℕ) : ℝ) := by
      apply (le_log_iff_exp_le hypos).2
      have he : exp 18 = exp 1 ^ 18 := by rw [← exp_nat_mul]; norm_num
      have hp := pow_le_pow_left₀ (exp_pos 1).le
        (show exp 1 ≤ (2.72 : ℝ) by linarith [exp_one_lt_d9]) 18
      rw [← he] at hp
      have hnR : (100000000 : ℝ) ≤ N := by exact_mod_cast hlarge8
      push_cast
      norm_num at hp
      linarith
    have hl26 : log ((2 * N + 1 : ℕ) : ℝ) ≤ 26 :=
      (log_le_log hypos (by push_cast; linarith : ((2 * N + 1 : ℕ) : ℝ) ≤ ((2 * N + 6 : ℕ) : ℝ))).trans hlog26
    have hp := OddGoldbach21.primeCounting_lower18 (2 * N + 1) hn1340 hl18
    have hp' := (div_le_iff₀ hlogpos).1 hp
    have hmul := mul_le_mul_of_nonneg_left hl26 hpi0
    have hnR : (100000000 : ℝ) ≤ N := by exact_mod_cast hlarge8
    push_cast at hp' hmul
    nlinarith only [hp', hmul, hcountR, hnR]

#print axioms solution


