-- Prove2me | solution 1 for QueryMachines.stLiftRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:24:07.645943+00:00
-- url     : https://prove2.me/submissions/ce2f0c4a-c9d3-4fb9-99e7-3bf5a0fce910

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
open QueryMachines
open Groundwork Finset QueryMachine

theorem solution : StLiftRuns := by
  intro Q A α β R O a t S b h
  have aux : ∀ {s : R.σ}, R.Reaches S b s t →
      (QueryMachine.lift R : QueryMachine Q A α β).Reaches O S b s t [] := by
    clear h
    intro s h
    induction h with
    | halt ho hs => exact .halt ho hs
    | step ho hs _ ih => exact .step ho rfl hs ih
  exact aux h
