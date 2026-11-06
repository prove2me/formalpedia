-- Prove2me | solution 1 for P2M_Printed_asked___close_e2c625851c76
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:00.583926+00:00
-- url     : https://prove2.me/submissions/4cf03512-d9cb-4389-893b-2482b1b9c694

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
theorem _root_.solution (O : NetQuery → Option ℤ) : (asked.close O).Ψ = Stepped.ofOption fun a : NetInput × PsiQ => O (Sum.inr (Sum.inr (Sum.inl a.2))) := close_query _ _
end Printed
