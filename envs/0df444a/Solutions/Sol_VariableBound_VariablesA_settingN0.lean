-- Prove2me | solution 1 for VariableBound.VariablesA.settingN0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:50.730051+00:00
-- url     : https://prove2.me/submissions/a7305aba-9b6f-48ee-a9f7-cc7f4c4f3ab8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Theorems.Thm_VariableBound_VariablesA_lg_le_id
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_VariablesA_lg_le_self


set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open MainTheoremForms
namespace VariableBound.VariablesA
theorem _root_.solution (hP : VariableBound.ParamIneq) : SettingN0Stmt := by
  intro C₀ hC
  refine ⟨2 ^ ((640 * C₀ ^ 2) ^ 2), fun n k Δ hn hk4 hΔ hΔy => ?_⟩
  have hC' : (1 : ℝ) ≤ C₀ := by exact_mod_cast hC
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hy : (((640 * C₀ ^ 2) ^ 2 : ℕ) : ℝ) ≤ MainTheoremForms.lg n := by
    rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact_mod_cast hn
  push_cast at hy
  set y : ℝ := MainTheoremForms.lg n with hydef
  have hy640 : (640 : ℝ) ^ 2 ≤ y := by
    refine le_trans ?_ hy
    have : (640 : ℝ) ≤ 640 * (C₀ : ℝ) ^ 2 := by nlinarith [one_le_pow₀ hC' (n := 2)]
    exact pow_le_pow_left₀ (by norm_num) this 2
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  set t : ℝ := y ^ (1 / 4 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hy0 _
  have ht4 : t ^ 4 = y := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hkt : (k : ℝ) ≤ t := by
    rw [← ht4] at hk4
    exact (pow_le_pow_iff_left₀ (by positivity) ht0.le (by norm_num)).1 hk4
  have hz : MainTheoremForms.lg y = 4 * MainTheoremForms.lg t := by
    rw [← ht4, MainTheoremForms.lg, Real.logb_pow]
    norm_num [MainTheoremForms.lg]
  have hz0 : 0 ≤ MainTheoremForms.lg y := Real.logb_nonneg (by norm_num) hy1
  have hzt : MainTheoremForms.lg y ≤ 4 * t := by
    rw [hz]
    linarith [lg_le_id ht0]
  have ht2 : 640 * (C₀ : ℝ) ^ 2 ≤ t ^ 2 := by
    have h1 : (640 * (C₀ : ℝ) ^ 2) ^ 2 ≤ (t ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
      rw [ht4]
      exact hy
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  -- log Δ ≤ 4kC₀·log log n
  have h1 : MainTheoremForms.lg Δ ≤ 4 * k * C₀ * MainTheoremForms.lg y := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hΔ0 hΔy
    rw [Real.logb_pow] at this
    push_cast at this
    exact this
  have h2 : 4 * (k : ℝ) * C₀ * MainTheoremForms.lg y ≤ 4 * C₀ * t * MainTheoremForms.lg y := by
    have : 4 * (k : ℝ) * C₀ ≤ 4 * C₀ * t := by nlinarith
    exact mul_le_mul_of_nonneg_right this hz0
  -- log Δ ≤ log n/(40C₀)
  have h3 : MainTheoremForms.lg Δ ≤ 1 / (40 * C₀ : ℝ) * y := by
    have g1 : 4 * (C₀ : ℝ) * t * MainTheoremForms.lg y ≤ 16 * C₀ * t ^ 2 := by
      have : 4 * (C₀ : ℝ) * t * MainTheoremForms.lg y ≤ 4 * C₀ * t * (4 * t) := mul_le_mul_of_nonneg_left hzt (by positivity)
      nlinarith
    have g2 : 16 * (C₀ : ℝ) * t ^ 2 ≤ 1 / (40 * C₀ : ℝ) * y := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), ← ht4]
      have : 640 * (C₀ : ℝ) ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right ht2 (by positivity)
      nlinarith
    linarith
  have h4 : (Δ : ℝ) ≤ (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) := by
    have hp : 0 < (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) := Real.rpow_pos_of_pos hn0 _
    refine (Real.logb_le_logb (b := 2) (by norm_num) hΔ0 hp).1 ?_
    rw [Real.logb_rpow_eq_mul_logb_of_pos hn0]
    exact h3
  -- log(2Δ) ≤ 1 + log n/40, and log n ≤ n
  have h5 : MainTheoremForms.lg (2 * Δ) = 1 + MainTheoremForms.lg Δ := by
    rw [MainTheoremForms.lg, Real.logb_mul (by norm_num) hΔ0.ne', Real.logb_self_eq_one (by norm_num)]
    rfl
  have h6 : MainTheoremForms.lg Δ ≤ y / 40 := by
    refine h3.trans ?_
    rw [one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hy0.le (by norm_num) (by linarith)
  have h7 : y ≤ n := lg_le_self n
  have h8 : 29 * MainTheoremForms.lg (2 * Δ) + 19 ≤ n := by
    rw [h5]
    linarith
  have h9 : 0 ≤ MainTheoremForms.lg Δ := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ Δ))
  refine ⟨h1, h2, h4, by rw [h5] at h8 ⊢; linarith, fun m nb rb hnb hm hNb hRb => hP.large n Δ m nb rb hΔ hnb hm hNb hRb h8⟩
end VariableBound.VariablesA
