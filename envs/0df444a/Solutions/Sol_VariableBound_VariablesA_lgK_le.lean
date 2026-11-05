-- Prove2me | solution 1 for VariableBound.VariablesA.lgK_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:31.555316+00:00
-- url     : https://prove2.me/submissions/f6de752e-38be-4fb5-b59f-f94c735d2702

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
import Theorems.Thm_VariableBound_VariablesA_K_le_n
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {n l : ℕ} (h : IsLevel S Q n l) : MainTheoremForms.lg (S.K (Q.idx l)) ≤ MainTheoremForms.lg n := by
  have h2 : (2 : ℝ) ≤ S.K (Q.idx l) := by exact_mod_cast Q.K_two l
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by exact_mod_cast K_le_n Q h)
end VariableBound.VariablesA
