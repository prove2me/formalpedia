-- Prove2me | solution 1 for PrintedOrder.stHosted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:50.62177+00:00
-- url     : https://prove2.me/submissions/a75df70f-a8c1-428c-a8f4-7b5e37953dbf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitSat_Main
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Deciding
import Theorems.Thm_PrintedOrder_hostedFrom
import Theorems.Thm_SplitSat_stImplication


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
namespace PrintedOrder
theorem _root_.solution : StHosted := hostedFrom SplitSat.stImplication
end PrintedOrder
