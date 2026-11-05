-- Prove2me | solution 1 for WidthK.Thresholds.exists_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:40:22.073898+00:00
-- url     : https://prove2.me/submissions/79527511-40b0-49e4-911f-fccd01a8bc01

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
import Theorems.Thm_WidthK_Thresholds_two_le_bsum
import Theorems.Thm_WidthK_Thresholds_bsum_le_pow
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open WidthK WidthK.Thresholds
open Finset
namespace WidthK.Thresholds
theorem _root_.solution (k τ₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, τ₀ ≤ τ ∧ 4 ≤ τ ∧
      ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsum τ k : ℝ)) ≤ ε := by
  set E : ℕ := 2 ^ (k + 1) + 1 with hE
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (4 * (k : ℝ) * (E : ℝ) / ε)
  set m : ℕ := max (max 2 τ₀) m₀ with hm
  have hm2 : 2 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmτ : τ₀ ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmr2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hmε : 4 * (k : ℝ) * (E : ℝ) / ε ≤ (m : ℝ) := hm₀.trans (by exact_mod_cast le_max_right _ m₀)
  have hmε' : 4 * (k : ℝ) * (E : ℝ) ≤ ε * (m : ℝ) := by
    rw [div_le_iff₀ hε] at hmε; linarith
  have h4 : 4 ≤ m ^ 2 := by nlinarith
  refine ⟨m ^ 2, le_trans hmτ (Nat.le_self_pow (by norm_num) _), h4, ?_⟩
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := by
    rw [hE]; push_cast; have : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢; linarith
  have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hm0
  have hB : (bsum (m ^ 2) k : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) ^ 2 ^ (k + 1) := by
    exact_mod_cast bsum_le_pow h4 k
  have hB0 : (0 : ℝ) < (bsum (m ^ 2) k : ℝ) := by
    have := two_le_bsum (m ^ 2) k
    exact_mod_cast (by omega : 0 < bsum (m ^ 2) k)
  have hle : Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ) ≤ Real.exp 1 * (m : ℝ) ^ (2 * E) := by
    have e1 : Real.exp 1 * (m : ℝ) ^ (2 * E) = Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((m ^ 2 : ℕ) : ℝ) ^ 2 ^ (k + 1) := by
      rw [hE]; push_cast; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hlog : Real.log (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ)) ≤ 2 * (E : ℝ) * (m : ℝ) := by
    have hpos : 0 < Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ) := by positivity
    refine le_trans (Real.log_le_log hpos hle) ?_
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    nlinarith
  have hlogb : Real.logb 2 (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ)) ≤ 4 * (E : ℝ) * (m : ℝ) := by
    rw [← Real.log_div_log, div_le_iff₀ (by linarith)]
    have : 0 ≤ (E : ℝ) * (m : ℝ) := by positivity
    nlinarith
  calc ((k : ℝ) / ((m ^ 2 : ℕ) : ℝ)) * Real.logb 2 (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ))
      ≤ ((k : ℝ) / ((m ^ 2 : ℕ) : ℝ)) * (4 * (E : ℝ) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogb (by positivity)
    _ = 4 * (k : ℝ) * (E : ℝ) / (m : ℝ) := by push_cast; field_simp
    _ ≤ ε := by rw [div_le_iff₀ hm0]; exact hmε'
end WidthK.Thresholds
