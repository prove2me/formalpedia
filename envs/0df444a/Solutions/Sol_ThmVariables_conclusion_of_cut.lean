-- Prove2me | solution 1 for ThmVariables.conclusion_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:57.221197+00:00
-- url     : https://prove2.me/submissions/8672bc9d-9820-4e23-8ab1-b07561b74ea4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ThmVariables_PartA
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_ThmVariables_boundAtANumberBetween
import Theorems.Thm_ThmVariables_e_pos
import Theorems.Thm_VariableBound_VariablesA_e_pos


set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)
namespace ThmVariables
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ C₀' : ℕ} {num : List Unit × List Unit → ℕ × ℕ} (Q : S.Seq (cutNumber K num) C₀')
    (hL : Levels K e C₀) (hnum : CliqueLevels.NumberBetween K e num) (hK : ∀ l : ℕ, S.K (Q.idx l) = K l) {M : TM2ComputableAux Bool Bool} {C' : ℕ} (hM : ThmVariablesAFor S Q M C') :
    Conclusion K e M (2 * C') := by
  intro k n l φ hl hk hk4 hφ
  have hl' : MainTheoremForms.IsLevel S Q n l := by
    unfold MainTheoremForms.IsLevel
    rw [hK, hK]
    exact hl
  obtain ⟨ev⟩ := hM k n l φ hl' hk hk4 hφ
  obtain ⟨h1, h2⟩ := hnum.2 l
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (boundAtANumberBetween C' k n (e l) (cutNumber K num l) (by omega) (e_pos hL l)
    (le_min h1 (hL.e_le l)) ((min_le_left _ _).trans h2) (min_le_right _ _))⟩⟩
end ThmVariables
