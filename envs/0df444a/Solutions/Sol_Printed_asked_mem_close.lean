-- Prove2me | solution 1 for Printed.asked_mem_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:30.993316+00:00
-- url     : https://prove2.me/submissions/391b4254-674e-47e4-a6b1-41ac08822212

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_query
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_query



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (O : NetQuery → Option ℤ) :
    (asked.close O).mem = Stepped.mapOut (Stepped.ofOption fun a : NetInput × WQ => O (Sum.inl a.2)) fun v : ℤ => decide (v ≠ 0) := by
  change (QueryMachine.mapOut (QueryMachine.query fun x : NetInput × WQ => (Sum.inl x.2 : NetQuery)) fun v : ℤ => decide (v ≠ 0)).close O = _
  rw [close_mapOut, close_query]
end Printed
