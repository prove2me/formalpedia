-- Prove2me | solution 1 for VariableBound.VariablesA.stepSparsifyLarge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:28:16.093194+00:00
-- url     : https://prove2.me/submissions/f21ee989-a7df-4e82-a6b1-ba2236cf6d6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Theorems.Thm_ClauseBound_Alg_End_log_pow_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.VariablesA
theorem _root_.solution : StepSparsifyLargeStmt := by
  intro C₀
  set c₃ : ℕ := 3 * (C₀ + 3).factorial * 2 ^ (C₀ + 3) with hc₃
  have hc₃1 : 1 ≤ c₃ := by
    have := Nat.factorial_pos (C₀ + 3)
    have h2 : 0 < 2 ^ (C₀ + 3) := by positivity
    have : 0 < 3 * (C₀ + 3).factorial * 2 ^ (C₀ + 3) := by positivity
    omega
  refine ⟨2 ^ c₃, fun k n x hn hk4 hx => ?_⟩
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hy : (c₃ : ℝ) ≤ MainTheoremForms.lg n := by
    rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact_mod_cast hn
  have hc₃' : (1 : ℝ) ≤ c₃ := by exact_mod_cast hc₃1
  have hy1 : 1 ≤ MainTheoremForms.lg n := hc₃'.trans hy
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  -- k ≤ log n
  have hky : (k : ℝ) ≤ MainTheoremForms.lg n := by
    refine le_trans ?_ hk4
    exact_mod_cast Nat.le_self_pow (by norm_num) k
  -- (log n)^(C₀+3) ≤ c₃·n, hence (log n)^(C₀+2) ≤ n
  have h1 : MainTheoremForms.lg n ^ (C₀ + 3) ≤ (c₃ : ℝ) * n := by
    refine le_trans (pow_le_pow_left₀ hy0.le ?_ _) (log_pow_le (C₀ + 3) hn1)
    exact Real.logb_le_logb_of_le (by norm_num) hn0 (by linarith)
  have h2 : MainTheoremForms.lg n ^ (C₀ + 2) ≤ n := by
    have h3 : (c₃ : ℝ) * MainTheoremForms.lg n ^ (C₀ + 2) ≤ (c₃ : ℝ) * n := by
      refine le_trans ?_ h1
      rw [pow_succ (MainTheoremForms.lg n) (C₀ + 2), mul_comm (MainTheoremForms.lg n ^ (C₀ + 2))]
      exact mul_le_mul_of_nonneg_right hy (by positivity)
    exact le_of_mul_le_mul_left h3 (by linarith)
  have h4 : MainTheoremForms.lg n ^ 2 ≤ 1 / MainTheoremForms.lg n ^ C₀ * n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
    rwa [add_comm] at h2
  calc (k : ℝ) * MainTheoremForms.lg n ≤ MainTheoremForms.lg n * MainTheoremForms.lg n := mul_le_mul_of_nonneg_right hky hy0.le
    _ = MainTheoremForms.lg n ^ 2 := (sq _).symm
    _ ≤ 1 / MainTheoremForms.lg n ^ C₀ * n := h4
    _ ≤ x * n := mul_le_mul_of_nonneg_right hx hn0.le
end VariableBound.VariablesA
