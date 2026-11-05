-- Prove2me | solution 1 for RecursionToBound.cutOffIsIdle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:38:33.188345+00:00
-- url     : https://prove2.me/submissions/7c5f01e2-9f05-4091-82a0-af9d5adb859b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : CutOffIsIdle := by
  intro k n hn h
  unfold kcU
  refine min_eq_left ?_
  have hk : (k : ℝ) ≤ lg n := le_trans (by exact_mod_cast Nat.le_self_pow (by norm_num) k) h
  have h2 : (2 : ℝ) ^ k ≤ n := by
    have := (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hn)).1 hk
    rwa [Real.rpow_natCast] at this
  have h3 : 2 ^ k ≤ n := by exact_mod_cast h2
  exact Nat.le_log_of_pow_le (by norm_num) (h3.trans (Nat.le_succ n))
end RecursionToBound
