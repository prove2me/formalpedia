-- Prove2me | solution 1 for Printed.clique_groupTables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:55.46507+00:00
-- url     : https://prove2.me/submissions/b1d7c18d-181f-408b-bdf7-30c46e7ba2bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) :
    (clique K L fun w => groupTables N P B hK0 x L w.val) = Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L :=
  congrArg (clique K L) (funext fun w => funext fun _ => dif_pos w.2)
end Printed
