-- Prove2me | solution 1 for QueryMachines.QueryMachine.Reaches.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:58.129398+00:00
-- url     : https://prove2.me/submissions/5c4fd9c9-d0ca-412a-8763-e0b492fa5274

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
namespace QueryMachines.QueryMachine
namespace Reaches
theorem _root_.solution {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') : M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)
end Reaches
end QueryMachines.QueryMachine
