-- Prove2me | solution 1 for VariableBound.VariablesA.e_ge_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:17.772259+00:00
-- url     : https://prove2.me/submissions/bd93a967-c5c4-4c65-90cf-53a9781c85ee

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
import Theorems.Thm_VariableBound_VariablesA_lgK_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {n l : ℕ} (h : IsLevel S Q n l) : 1 / MainTheoremForms.lg n ^ C₀ ≤ e l := by
  have h1 := one_le_lgK Q l
  refine le_trans ?_ (Q.e_ge l)
  exact one_div_le_one_div_of_le (by have : 0 < MainTheoremForms.lg (S.K (Q.idx l)) := by linarith
                                     exact pow_pos this _) (pow_le_pow_left₀ (by linarith) (lgK_le Q h) _)
end VariableBound.VariablesA
