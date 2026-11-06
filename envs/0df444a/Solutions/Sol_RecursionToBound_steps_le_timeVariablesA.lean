-- Prove2me | solution 1 for RecursionToBound.steps_le_timeVariablesA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:28.598856+00:00
-- url     : https://prove2.me/submissions/f0b7570c-7178-4d91-b579-9271593cd7b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_End
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PairsToBound_choice_le
import Theorems.Thm_PairsToBound_natCast_pow_eq


set_option autoImplicit false
section
section
open RecursionToBound
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution (q a : ℕ) {k n E len : ℕ} {e : ℝ} (h1 : 1 ≤ (a : ℝ) * expVariablesA k n e) (hE : (E : ℝ) ≤ (a : ℝ) * expVariablesA k n e)
    (hk : (k : ℝ) * lg n ≤ (a : ℝ) * expVariablesA k n e) (hn : 4 ≤ n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (len + 2 ^ E + 1) ^ q ≤ timeVariablesA (q * 12 * a) k n e := by
  have h0 : 0 ≤ (a : ℝ) * expVariablesA k n e := by linarith
  have t1 : ((2 ^ E : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * ((a : ℝ) * expVariablesA k n e)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    push_cast
    linarith
  have t2 : ((len + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((10 : ℕ) : ℝ) * ((a : ℝ) * expVariablesA k n e)) := by
    have g1 : (n + 2) ^ (5 * k) ≤ n ^ (10 * k) := by
      calc (n + 2) ^ (5 * k) ≤ (n ^ 2) ^ (5 * k) := Nat.pow_le_pow_left (by nlinarith) _
        _ = n ^ (10 * k) := by rw [← pow_mul, show 2 * (5 * k) = 10 * k by ring]
    calc ((len + 1 : ℕ) : ℝ) ≤ ((n ^ (10 * k) : ℕ) : ℝ) := by exact_mod_cast hlen.trans g1
      _ = (2 : ℝ) ^ (((10 * k : ℕ) : ℝ) * lg n) := by rw [Nat.cast_pow, natCast_pow_eq (by omega)]
      _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        linarith
  have h := choice_le q 10 h1 t1 t2
  rw [Nat.add_comm len (2 ^ E)]
  refine h.trans (le_of_eq ?_)
  unfold timeVariablesA
  congr 2
  push_cast
  ring
end RecursionToBound
