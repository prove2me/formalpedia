-- Prove2me | solution 1 for QueryMachines.QueryMachine.bind_reaches_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:05:53.547477+00:00
-- url     : https://prove2.me/submissions/5f9d7e81-802d-48b6-9569-6b7d55c8013d

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
theorem _root_.solution [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (bind M N).Reaches O (S + 1) c (.inr s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih
end QueryMachines.QueryMachine
