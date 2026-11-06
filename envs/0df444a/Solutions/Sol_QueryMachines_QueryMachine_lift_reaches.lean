-- Prove2me | solution 1 for QueryMachines.QueryMachine.lift_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:54.544942+00:00
-- url     : https://prove2.me/submissions/eb8c3915-347e-4e71-8ed7-c7e9852ba130

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_reaches_asksNothing


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution {R : Stepped α β} {O : Q → Option A} {S t : ℕ} {b : β} {s : R.σ} (h : R.Reaches S b s t) :
    (lift R : QueryMachine Q A α β).Reaches O S b s t [] := reaches_asksNothing h
end QueryMachines.QueryMachine
