-- Prove2me | solution 1 for VariableBound.VariablesA.pick_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:47.066613+00:00
-- url     : https://prove2.me/submissions/9146e545-a381-41c1-93fd-00cf87377255

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Theorems.Thm_VariableBound_VariablesA_eq_replicate
import Theorems.Thm_ClauseBound_TopN_Arith_eq_replicate
import Theorems.Thm_VariableBound_VariablesA_level_eq_pick


set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK MainTheoremForms
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
namespace VariableBound.VariablesA
theorem _root_.solution {n l : ℕ} (h : IsLevel S Q n l) : (Q.pick (root17 n)).1 = List.replicate l () := by
  rw [eq_replicate (Q.pick (root17 n)).1, level_eq_pick Q h]
end VariableBound.VariablesA
