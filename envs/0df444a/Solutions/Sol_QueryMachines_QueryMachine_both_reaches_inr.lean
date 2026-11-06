-- Prove2me | solution 1 for QueryMachines.QueryMachine.both_reaches_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:05:54.633853+00:00
-- url     : https://prove2.me/submissions/1183a5e1-46c1-4714-946d-a4f140aab55d

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
theorem _root_.solution [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (both M N).Reaches O (size b + S + 1) (b, c) (.inr (b, s)) t L := by
  induction h with
  | @halt s t ho hs => exact .halt (by change (N.out s).map _ = _; rw [ho]; rfl) (by change size b + size s + 1 ≤ _; omega)
  | @step s t L ho ha hs _ ih => exact .step (by change (N.out s).map _ = _; rw [ho]; rfl) ha (by change size b + size s + 1 ≤ _; omega) ih
  | @query s t L x v ho ha hv hs _ ih => exact .query (by change (N.out s).map _ = _; rw [ho]; rfl) ha hv (by change size b + size s + 1 ≤ _; omega) ih
end QueryMachines.QueryMachine
