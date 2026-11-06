-- Prove2me | solution 1 for PrintedOrder.eth_and_seth_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:11:15.799373+00:00
-- url     : https://prove2.me/submissions/f49f8e19-1a72-4819-a4ba-f5546e8d6b10

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
import Theorems.Thm_PrintedOrder_stThreeSatFamily
import Theorems.Thm_PrintedOrder_stHosted
import Theorems.Thm_PrintedOrder_endThroughImplication
import Theorems.Thm_SplitSat_stTiedThreeTM


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
namespace PrintedOrder
theorem _root_.solution : EthAndSethAgain := endThroughImplication stThreeSatFamily stHosted SplitSat.stTiedThreeTM
end PrintedOrder
