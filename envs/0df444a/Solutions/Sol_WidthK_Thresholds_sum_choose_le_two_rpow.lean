-- Prove2me | solution 1 for WidthK.Thresholds.sum_choose_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:54.327912+00:00
-- url     : https://prove2.me/submissions/cd07b71d-adf1-4ad3-a0f7-9dc5b688fa79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SparsifyWidthK_Thresholds
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_pow_mul_sum_choose_le_exp
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
open Groundwork.Sparsify
namespace WidthK.Thresholds
theorem _root_.solution {k τ L : ℕ} (hτ : 1 ≤ τ) (hkL : k ≤ L) {ε : ℝ}
    (h : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) ≤ ε) (n : ℕ) :
    ((∑ j ∈ range (k * n / τ + 1), (L * n).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hε : 0 ≤ ε := by simpa using h
    simp only [zero_mul, Nat.zero_div, zero_add, range_one, Finset.sum_singleton, Nat.choose_zero_right,
      Nat.cast_one]
    exact Real.one_le_rpow one_le_two (by positivity)
  have ht0 : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
  have ht1 : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkL' : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  set S : ℝ := ((∑ j ∈ range (k * n / τ + 1), (L * n).choose j : ℕ) : ℝ) with hS
  set b : ℝ := (τ : ℝ) * (L : ℝ) / (k : ℝ) with hb
  set ρ : ℝ := (k : ℝ) * (n : ℝ) / (τ : ℝ) with hρ
  have hb1 : 1 ≤ b := by
    rw [hb, le_div_iff₀ hk0]; nlinarith
  have hb0 : 0 < b := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hr : k * n / τ ≤ L * n :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_right _ hkL)
  have hrρ : ((k * n / τ : ℕ) : ℝ) ≤ ρ := by
    have := @Nat.cast_div_le ℝ _ _ _ (k * n) τ
    rw [hρ]; push_cast at this; exact this
  have hkey : b⁻¹ ^ (k * n / τ) * S ≤ Real.exp ρ := by
    have hx : ((L * n : ℕ) : ℝ) * b⁻¹ = ρ := by
      rw [hb, hρ]; push_cast; field_simp
    rw [← hx]
    exact pow_mul_sum_choose_le_exp (inv_pos.mpr hb0) (inv_le_one_of_one_le₀ hb1) hr
  have hS1 : S ≤ b ^ (k * n / τ) * Real.exp ρ := by
    rw [inv_pow] at hkey
    have hp : 0 < b ^ (k * n / τ) := by positivity
    calc S = b ^ (k * n / τ) * ((b ^ (k * n / τ))⁻¹ * S) := by field_simp
      _ ≤ b ^ (k * n / τ) * Real.exp ρ := mul_le_mul_of_nonneg_left hkey hp.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hy : 0 < Real.exp 1 * (τ : ℝ) * (L : ℝ) := by positivity
  calc S ≤ b ^ (k * n / τ) * Real.exp ρ := hS1
    _ = b ^ ((k * n / τ : ℕ) : ℝ) * Real.exp ρ := by rw [Real.rpow_natCast]
    _ ≤ b ^ ρ * Real.exp ρ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb1 hrρ) (Real.exp_pos ρ).le
    _ = (b * Real.exp 1) ^ ρ := by rw [Real.mul_rpow hb0.le he.le, Real.exp_one_rpow]
    _ ≤ (Real.exp 1 * (τ : ℝ) * (L : ℝ)) ^ ρ := by
        refine Real.rpow_le_rpow (by positivity) ?_ hρ0
        have : b ≤ (τ : ℝ) * (L : ℝ) := by
          rw [hb]; exact div_le_self (by positivity) hk1
        nlinarith
    _ = (2 : ℝ) ^ (Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * ρ) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hy]
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        calc Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * ρ
            = ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * (n : ℝ) := by rw [hρ]; ring
          _ ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_right h hn
end WidthK.Thresholds
