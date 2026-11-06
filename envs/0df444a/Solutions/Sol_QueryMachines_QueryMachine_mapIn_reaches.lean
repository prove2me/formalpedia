-- Prove2me | solution 1 for QueryMachines.QueryMachine.mapIn_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:05:00.626944+00:00
-- url     : https://prove2.me/submissions/8c7e8103-8137-46a5-b707-581ea635a8e7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {c : γ} {s : M.σ}
    (hr : M.Reaches O S c s own L) : (mapIn g M).Reaches O S c s own L := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih => exact .step ho ha hs ih
  | query ho ha hv hs _ ih => exact .query ho ha hv hs ih
end QueryMachines.QueryMachine
