-- Prove2me | solution 1 for VariableBound.VariablesA.level_eq_pick
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:26.046178+00:00
-- url     : https://prove2.me/submissions/615e35d1-fe97-45eb-9242-c7db03a7336c

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
import Theorems.Thm_VariableBound_VariablesA_K_strictMono
import Theorems.Thm_VariableBound_VariablesA_level_unique
import Theorems.Thm_VariableBound_VariablesA_isLevel_pick
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {n l : ℕ} (h : IsLevel S Q n l) : (Q.pick (root17 n)).1.length = l := by
  have h0 : S.K (Q.idx 0) ^ 17 ≤ n := (Nat.pow_le_pow_left ((K_strictMono Q).monotone (Nat.zero_le l)) 17).trans h.1
  exact level_unique Q (isLevel_pick Q h0) h
end VariableBound.VariablesA
