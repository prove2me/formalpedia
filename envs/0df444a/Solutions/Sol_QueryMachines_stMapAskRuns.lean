-- Prove2me | solution 1 for QueryMachines.stMapAskRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:48:59.49613+00:00
-- url     : https://prove2.me/submissions/55ef1b3e-8ece-464e-a6c6-3a74112fbce0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
set_option autoImplicit false

namespace QueryMachines.QueryMachine

open Groundwork Finset

variable {Q Q' A α β : Type}

theorem mapAsk_reaches_aux {h : Q → Q'} {M : QueryMachine Q A α β}
    {O : Q' → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches (fun x => O (h x)) S b s own L) :
    (mapAsk h M).Reaches O S b s own (L.map h) := by
  induction hr with
  | halt ho hs => exact .halt ho hs
  | step ho ha hs _ ih =>
      exact .step ho (by change (M.ask _).map h = none; rw [ha]; rfl) hs ih
  | query ho ha hv hs _ ih =>
      exact .query ho (by change (M.ask _).map h = _; rw [ha]; rfl) hv hs ih

end QueryMachines.QueryMachine

open QueryMachines
open Groundwork Finset QueryMachine

theorem solution : StMapAskRuns := by
  intro Q Q' A α β h M O a own S L b hr
  exact QueryMachine.mapAsk_reaches_aux hr
