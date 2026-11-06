-- Prove2me | solution 1 for Printed.asked_W_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:33.870478+00:00
-- url     : https://prove2.me/submissions/645dffe8-2e7b-4cbd-b49f-7b035b4e5a82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_QueryMachines_QueryMachine_close_query
attribute [local simp] QueryMachines.QueryMachine.close_query



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (O : NetQuery → Option ℤ) : (asked.close O).W = Stepped.ofOption fun a : NetInput × WQ => O (Sum.inr (Sum.inl a.2)) := close_query _ _
end Printed
