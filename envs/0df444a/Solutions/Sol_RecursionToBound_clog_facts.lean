-- Prove2me | solution 1 for RecursionToBound.clog_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:55:39.488362+00:00
-- url     : https://prove2.me/submissions/68937fd4-33e6-48e7-ad9e-65df58ea2e3d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
import Theorems.Thm_VariableBound_Net_Main_p
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ^ Nat.clog 2 Δ ≤ 2 * Δ ∧ 1 ≤ Nat.clog 2 Δ ∧ ((Nat.clog 2 Δ + 1 : ℕ) : ℝ) ≤ 3 * lg Δ := by
  have h1 : 1 ≤ Nat.clog 2 Δ := Nat.clog_pos (by norm_num) hΔ
  obtain ⟨p, hp⟩ : ∃ p, Nat.clog 2 Δ = p + 1 := ⟨Nat.clog 2 Δ - 1, by omega⟩
  have h2 : 2 ^ p < Δ := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := Δ) (by omega)
    rwa [hp, Nat.pred_succ] at this
  refine ⟨by rw [hp, pow_succ]; omega, h1, ?_⟩
  have h3 : (p : ℝ) ≤ lg Δ := by
    refine (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast (by omega : 0 < Δ))).2 ?_
    rw [Real.rpow_natCast]
    exact_mod_cast h2.le
  have h4 := one_le_lg hΔ
  rw [hp]
  push_cast
  linarith
end RecursionToBound
