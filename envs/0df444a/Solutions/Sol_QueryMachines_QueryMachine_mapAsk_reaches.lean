-- Prove2me | solution 1 for QueryMachines.QueryMachine.mapAsk_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:55.562872+00:00
-- url     : https://prove2.me/submissions/299c9b29-181a-4bd9-9ba6-ed481451460f

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
theorem _root_.solution {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches (fun x => O (h x)) S b s own L) : (mapAsk h M).Reaches O S b s own (L.map h) := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho (by change (M.ask _).map h = none; rw [ha]; rfl) hs ih
  | query ho ha hv hs _ ih => exact .query ho (by change (M.ask _).map h = _; rw [ha]; rfl) hv hs ih
end QueryMachines.QueryMachine
