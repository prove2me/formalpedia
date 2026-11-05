-- Prove2me | solution 1 for VariableBound.VariablesA.one_le_lgK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:27:21.966205+00:00
-- url     : https://prove2.me/submissions/a86b2afd-252d-4427-8460-25f5b14f56ac

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution (l : ℕ) : 1 ≤ MainTheoremForms.lg (S.K (Q.idx l)) := by
  have h : (2 : ℝ) ≤ S.K (Q.idx l) := by exact_mod_cast Q.K_two l
  rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact h
end VariableBound.VariablesA
