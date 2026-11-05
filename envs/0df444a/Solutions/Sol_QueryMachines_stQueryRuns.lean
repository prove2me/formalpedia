-- Prove2me | solution 1 for QueryMachines.stQueryRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:23:59.677518+00:00
-- url     : https://prove2.me/submissions/8301ac49-6121-41e6-beec-76d7de6744e4

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
namespace QueryMachines
theorem _root_.solution : StQueryRuns := fun _ _ _ _ _ _ _ a v hv =>
  .query rfl rfl hv (by change size a + 1 ≤ _; omega) (.halt rfl (by change size v + 1 ≤ _; omega))
end QueryMachines
