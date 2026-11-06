-- Prove2me | solution 1 for QueryMachines.QueryMachine.branch_reaches_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:04.209356+00:00
-- url     : https://prove2.me/submissions/c122ce53-ed6f-4e4d-925a-696c042b1f0a

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
theorem _root_.solution {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₁.σ}
    (h : M₁.Reaches O S b s t L) : (branch sel M₁ M₂).Reaches O (S + 1) b (.inl s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih
end QueryMachines.QueryMachine
