-- Prove2me | solution 1 for ThmVariables.inParticular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:41:32.209469+00:00
-- url     : https://prove2.me/submissions/1d333741-c7bb-42a4-9135-3bba140781c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ThmVariables_Bound
import Theorems.Thm_ThmVariables_exists_level
import Theorems.Thm_ThmVariables_e_pos
import Theorems.Thm_ThmVariables_e_ge_n
import Theorems.Thm_ThmVariables_lg_lt
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_RecursionToBound_lg_div_le
import Theorems.Thm_VariableBound_VariablesA_e_ge_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_lg_div_facts
import Theorems.Thm_VariableBound_VariablesA_lg_lt


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution : InParticular := by
  intro K e C₀ hL α' c hα he M C hM
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ⌈((17 * C₀ : ℕ) : ℝ) ^ α'⌉₊ := ⟨_, rfl⟩
  refine ⟨C * (c * R * (C₀ + 1)), fun k n φ hn hk hk4 hφ => ?_⟩
  obtain ⟨l, hl⟩ := exists_level hL hn
  obtain ⟨ev⟩ := hM k n l φ hl hk hk4 hφ
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast hL.C₀_pos
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ lg n := (one_le_pow₀ (by linarith)).trans hk4
  have hy0 : 0 < lg n := by linarith
  have hyy : 0 ≤ lg (lg n) := Real.logb_nonneg (by norm_num) hy
  have he0 := e_pos hL l
  have f1 : lg n / (17 * C₀) < lg (K l) := by
    rw [div_lt_iff₀ (by positivity)]
    have := lg_lt hL hl
    linarith
  have f2 := RecursionToBound.lg_div_le (k := k) (by omega) hk4 (e_ge_n hL hl)
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 (hL.e_le l)
  have hw0 : 0 ≤ lg (k / e l) := by linarith
  have h1 : e l ≤ (c : ℝ) * R / lg n ^ α' := by
    refine (he l).trans ?_
    have g0 : (0 : ℝ) < ((17 * C₀ : ℕ) : ℝ) := by push_cast; positivity
    have g1 : (lg n / ((17 * C₀ : ℕ) : ℝ)) ^ α' ≤ lg (K l) ^ α' := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      push_cast
      exact f1.le
    rw [Real.div_rpow hy0.le g0.le] at g1
    have g2 : 0 < lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    have g3 : 0 < ((17 * C₀ : ℕ) : ℝ) ^ α' := Real.rpow_pos_of_pos g0 _
    have g4 : ((17 * C₀ : ℕ) : ℝ) ^ α' ≤ R := hR ▸ Nat.le_ceil _
    have g5 : 0 < lg (K l) ^ α' := lt_of_lt_of_le (by positivity) g1
    rw [div_le_div_iff₀ g5 g2]
    have g6 : lg n ^ α' ≤ (R : ℝ) * lg (K l) ^ α' := by
      rw [div_le_iff₀ g3] at g1
      exact g1.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right g4 g5.le)
    calc (c : ℝ) * lg n ^ α' ≤ c * ((R : ℝ) * lg (K l) ^ α') := mul_le_mul_of_nonneg_left g6 (by positivity)
      _ = _ := by ring
  have h2 : lg (k / e l) ≤ ((C₀ : ℝ) + 1) * lg (lg n) := f2.trans (mul_le_mul_of_nonneg_right (by linarith) hyy)
  have h3 : expVariablesA k n (e l) ≤ ((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α') := by
    have g2 : 0 < lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    calc expVariablesA k n (e l) = (k : ℝ) ^ 2 * n * (e l * lg (k / e l)) := by rw [expVariablesA]; ring
      _ ≤ (k : ℝ) ^ 2 * n * (((c : ℝ) * R / lg n ^ α') * (((C₀ : ℝ) + 1) * lg (lg n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hw0 (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  rw [timeVariablesA, timeVariablesAAlpha]
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  calc (C : ℝ) * expVariablesA k n (e l) ≤ (C : ℝ) * (((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α')) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by push_cast; ring
end ThmVariables
