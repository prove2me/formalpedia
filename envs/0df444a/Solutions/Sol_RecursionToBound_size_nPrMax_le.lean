-- Prove2me | solution 1 for RecursionToBound.size_nPrMax_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:00:19.164652+00:00
-- url     : https://prove2.me/submissions/f42b140f-d4c0-4e2a-b323-c4ae5cc0cc10

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
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_VariableBound_Net_Main_nPrMax
import Theorems.Thm_VariableBound_Net_Main_size


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution (K n Δ : ℕ) : Nat.size (nPrMax K n Δ) ≤ 3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ) + 1 := by
  rw [Nat.size_le]
  unfold nPrMax PaddedDescent.F.Mark.nProf
  calc (objMax n Δ + 1) ^ (3 * K ^ 8 * (3 * K ^ 8) * 2) ≤ (2 ^ Nat.size (objMax n Δ)) ^ (3 * K ^ 8 * (3 * K ^ 8) * 2) := Nat.pow_le_pow_left (Nat.lt_size_self _) _
    _ = 2 ^ (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ)) := by rw [← pow_mul, Nat.mul_comm (Nat.size _)]
    _ < 2 ^ (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ) + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
end RecursionToBound
