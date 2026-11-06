-- Prove2me | solution 1 for SparsifyThenCount.stPlanUsed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:40.326247+00:00
-- url     : https://prove2.me/submissions/df0e7c24-d41f-4827-91e1-abec429f86ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_PlanUsedDefs
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SparsifyThenCount_PlanUsed
import Theorems.Thm_SparsifyThenCount_PlanUsedL_planD_enc
import Theorems.Thm_SparsifyThenCount_PlanUsedL_isKCNF_nil
import Theorems.Thm_SparsifyThenCount_PlanUsedL_eBD_nil
import Theorems.Thm_SparsifyThenCount_PlanUsedL_not_le_bound
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
open PlanUsedL
namespace SparsifyThenCount
theorem _root_.solution : StPlanUsed := by
  intro Idx _ S pick slU rn rm A h hr k hk
  obtain ⟨D, hD⟩ := h.timeN 1
  have hpos : (0 : ℝ) < 1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually (gt_mem_nhds hpos))
  refine ⟨max N (2 * (D + 1)), fun n hn φ hφ => ?_⟩
  rw [planD_enc S pick slU φ hk hφ]
  by_contra hne
  have hnone : planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length = none := by
    cases hp : planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length with
    | none => rfl
    | some v => rw [hp] at hne; exact absurd rfl hne
  have hn1 : 1 ≤ n := by have := (le_max_right N (2 * (D + 1))).trans hn; omega
  have ht := hD k n [] hk hn1 (isKCNF_nil k n)
  rw [eBD_nil S pick slU n hk, hnone, Option.getD_none, one_mul, pow_one] at ht
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hsmall : (D : ℝ) * (k : ℝ) ^ 2 * rn n ≤ 1 / 2 := by
    have h1 : rn n < 1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2) := hN n ((le_max_left _ _).trans hn)
    have h2 : (D : ℝ) * (k : ℝ) ^ 2 * rn n ≤ (D : ℝ) * (k : ℝ) ^ 2 * (1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h1.le (by positivity)
    have h3 : (D : ℝ) * (k : ℝ) ^ 2 * (1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2)) = (D : ℝ) / ((D : ℝ) + 1) * (1 / 2) := by
      field_simp
    have h4 : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h3] at h2
    linarith
  refine not_le_bound hsmall ((le_max_right _ _).trans hn) (le_trans ?_ ht)
  omega
end SparsifyThenCount
