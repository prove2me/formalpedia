-- Prove2me | solution 1 for VariableBound.VariablesA.e_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:29:46.364995+00:00
-- url     : https://prove2.me/submissions/e472660f-b598-4a88-9e1d-af4a1554247e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Theorems.Thm_VariableBound_VariablesA_one_le_lgK
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
include Q
namespace VariableBound.VariablesA
theorem _root_.solution (l : ℕ) : 0 < e l := by
  have h := one_le_lgK Q l
  have h1 : 0 < 1 / Real.logb 2 (S.K (Q.idx l)) ^ C₀ := by
    have : 0 < Real.logb 2 (S.K (Q.idx l)) := lt_of_lt_of_le one_pos h
    positivity
  exact lt_of_lt_of_le h1 (Q.e_ge l)
end VariableBound.VariablesA
