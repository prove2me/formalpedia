-- Prove2me | solution 1 for QueryMachines.QueryMachine.mapOut_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:05:43.406877+00:00
-- url     : https://prove2.me/submissions/71e47633-1a47-4859-8e78-d8e268026155

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (mapOut M g).Reaches O S (g b) s own L := by
  induction hr with
  | halt ho hs => exact .halt (by change (M.out _).map g = _; rw [ho]; rfl) hs
  | step ho ha hs _ ih => exact .step (by change (M.out _).map g = _; rw [ho]; rfl) ha hs ih
  | query ho ha hv hs _ ih => exact .query (by change (M.out _).map g = _; rw [ho]; rfl) ha hv hs ih
end QueryMachines.QueryMachine
