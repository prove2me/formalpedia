-- Prove2me | solution 1 for Printed.stGroupingTiedOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:39.313564+00:00
-- url     : https://prove2.me/submissions/af10cc65-6d79-4bb7-a473-4bcfb8c8f0a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
import Theorems.Thm_Printed_groupingMachine_computes
import Theorems.Thm_Printed_asked_isNetworkP


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution : StGroupingTiedOf := fun hS hStops hE hV hSub K _ _ _ hK h0 hM =>
  groupingMachine_computes hStops hE hV hSub (by omega) (by positivity) h0 hM fun N P B hN => hS K hK NetInput _ _ N P B 1 _ (asked_isNetworkP N hN)
end Printed
