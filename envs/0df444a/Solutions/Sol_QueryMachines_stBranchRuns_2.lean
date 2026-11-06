-- Prove2me | solution 2 for QueryMachines.stBranchRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:19.63708+00:00
-- url     : https://prove2.me/submissions/dba4e6fe-e0cf-4d06-9750-1d8485949b39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_branch_reaches_inl
import Theorems.Thm_QueryMachines_QueryMachine_branch_reaches_inr
import Theorems.Thm_Groundwork_Stepped_branch_reaches_inl
import Theorems.Thm_Groundwork_Stepped_branch_reaches_inr


set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine
namespace QueryMachines
theorem _root_.solution : StBranchRuns := fun _ _ _ _ _ _ sel M₁ M₂ _ a _ _ _ _ =>
  ⟨fun x hs h => by
    have e : (branch sel M₁ M₂).init a = .inl (M₁.init x) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inl h,
   fun y hs h => by
    have e : (branch sel M₁ M₂).init a = .inr (M₂.init y) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inr h⟩
end QueryMachines
