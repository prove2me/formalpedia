-- Prove2me | solution 1 for VariableBound.VariablesA.level_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:30.513995+00:00
-- url     : https://prove2.me/submissions/656274fb-065e-4462-820d-0636ecbbb65c

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
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {n l l' : ℕ} (h : IsLevel S Q n l) (h' : IsLevel S Q n l') : l = l' := by
  have key : ∀ a b : ℕ, IsLevel S Q n a → IsLevel S Q n b → ¬ a < b := by
    intro a b ha hb hab
    have h1 : S.K (Q.idx (a + 1)) ≤ S.K (Q.idx b) := (K_strictMono Q).monotone hab
    exact absurd ((Nat.pow_le_pow_left h1 17).trans hb.1) (not_le.2 ha.2)
  exact le_antisymm (not_lt.1 (key _ _ h' h)) (not_lt.1 (key _ _ h h'))
end VariableBound.VariablesA
