-- Prove2me | solution 1 for VariableBound.VariablesA.thmVariablesAInParticular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:04.601751+00:00
-- url     : https://prove2.me/submissions/cbd7e724-63a5-4ebc-9e20-c00028cdca73

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
import Theorems.Thm_VariableBound_VariablesA_stepSparsifyFacts
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_isLevel_pick
import Theorems.Thm_VariableBound_VariablesA_lg_div_facts
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.VariablesA
theorem _root_.solution : ThmVariablesAInParticular := by
  intro Idx _ S e C₀ Q α' c hα he M C hM
  set R : ℕ := ⌈((17 * C₀ : ℕ) : ℝ) ^ α'⌉₊ with hR
  refine ⟨C * (c * R * (C₀ + 1)), fun k n φ hn hk hk4 hφ => ?_⟩
  have hl := isLevel_pick Q hn
  set l := (Q.pick (ClauseBound.TopN.root17 n)).1.length with hldef
  obtain ⟨ev⟩ := hM k n l φ hl hk hk4 hφ
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  obtain ⟨f1, f2⟩ := stepSparsifyFacts Idx S e C₀ Q k n l hl (by omega) hk4
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast one_le_C₀ Q
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ MainTheoremForms.lg n := (one_le_pow₀ (by linarith)).trans hk4
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have hyy : 0 ≤ MainTheoremForms.lg (MainTheoremForms.lg n) := Real.logb_nonneg (by norm_num) hy
  have he0 := e_pos Q l
  obtain ⟨w1, w2⟩ := lg_div_facts hk he0 (Q.e_le l)
  have hw0 : 0 ≤ MainTheoremForms.lg (k / e l) := by linarith
  -- e ≤ c·R/(log n)^α′
  have h1 : e l ≤ (c : ℝ) * R / MainTheoremForms.lg n ^ α' := by
    refine (he l).trans ?_
    have g0 : (0 : ℝ) < ((17 * C₀ : ℕ) : ℝ) := by push_cast; positivity
    have g1 : (MainTheoremForms.lg n / ((17 * C₀ : ℕ) : ℝ)) ^ α' ≤ MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      push_cast
      exact f1.le
    rw [Real.div_rpow hy0.le g0.le] at g1
    have g2 : 0 < MainTheoremForms.lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    have g3 : 0 < ((17 * C₀ : ℕ) : ℝ) ^ α' := Real.rpow_pos_of_pos g0 _
    have g4 : ((17 * C₀ : ℕ) : ℝ) ^ α' ≤ R := Nat.le_ceil _
    have g5 : 0 < MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := lt_of_lt_of_le (by positivity) g1
    rw [div_le_div_iff₀ g5 g2]
    have g6 : MainTheoremForms.lg n ^ α' ≤ (R : ℝ) * MainTheoremForms.lg (S.K (Q.idx l)) ^ α' := by
      rw [div_le_iff₀ g3] at g1
      exact g1.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right g4 g5.le)
    calc (c : ℝ) * MainTheoremForms.lg n ^ α' ≤ c * ((R : ℝ) * MainTheoremForms.lg (S.K (Q.idx l)) ^ α') := mul_le_mul_of_nonneg_left g6 (by positivity)
      _ = _ := by ring
  have h2 : MainTheoremForms.lg (k / e l) ≤ ((C₀ : ℝ) + 1) * MainTheoremForms.lg (MainTheoremForms.lg n) := f2.trans (mul_le_mul_of_nonneg_right (by linarith) hyy)
  have h3 : expVariablesA k n (e l) ≤ ((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * MainTheoremForms.lg (MainTheoremForms.lg n) / MainTheoremForms.lg n ^ α') := by
    have g2 : 0 < MainTheoremForms.lg n ^ α' := Real.rpow_pos_of_pos hy0 _
    calc expVariablesA k n (e l) = (k : ℝ) ^ 2 * n * (e l * MainTheoremForms.lg (k / e l)) := by rw [expVariablesA]; ring
      _ ≤ (k : ℝ) ^ 2 * n * (((c : ℝ) * R / MainTheoremForms.lg n ^ α') * (((C₀ : ℝ) + 1) * MainTheoremForms.lg (MainTheoremForms.lg n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hw0 (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  rw [timeVariablesA, timeVariablesAAlpha]
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  calc (C : ℝ) * expVariablesA k n (e l) ≤ (C : ℝ) * (((c * R * (C₀ + 1) : ℕ) : ℝ) * ((k : ℝ) ^ 2 * n * MainTheoremForms.lg (MainTheoremForms.lg n) / MainTheoremForms.lg n ^ α')) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by push_cast; ring
end VariableBound.VariablesA
