-- Prove2me | solution 1 for SparsifyThenCount.PlanUsedL.not_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:28.286143+00:00
-- url     : https://prove2.me/submissions/3438be04-6682-43eb-84dd-1f5a25b8395d

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
open SparsifyThenCount.PlanUsedL
namespace SparsifyThenCount.PlanUsedL
theorem _root_.solution {D k n : ℕ} {r : ℝ} (hr : (D : ℝ) * (k : ℝ) ^ 2 * r ≤ 1 / 2) (hn : 2 * (D + 1) ≤ n) :
    ¬ (2 ^ n ≤ ⌊(D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r)⌋₊) := by
  intro h
  have h0 : (0 : ℝ) ≤ (D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) := by positivity
  have h1 : ((2 ^ n : ℕ) : ℝ) ≤ (D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) := (Nat.cast_le.2 h).trans (Nat.floor_le h0)
  have h2 : (D : ℝ) * (k : ℝ) ^ 2 * n * r ≤ (n : ℝ) / 2 := by
    have : (D : ℝ) * (k : ℝ) ^ 2 * n * r = (D : ℝ) * (k : ℝ) ^ 2 * r * n := by ring
    rw [this]
    have h3 := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg n)
    linarith
  have h3 : (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have h4 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num), add_halves, Real.rpow_natCast]
    push_cast
    rfl
  have h5 : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
  have h6 : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ D := by
    have h7 : (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (D : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← h4]
      exact h1.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D))
    exact le_of_mul_le_mul_right h7 h5
  have h8 : (2 : ℝ) ^ (((D + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : ((2 * (D + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this ⊢
    linarith
  have h9 : ((D + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (((D + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self
  have h10 : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; rfl
  linarith
end SparsifyThenCount.PlanUsedL
