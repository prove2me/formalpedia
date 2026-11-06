-- Prove2me | solution 1 for PrintedOrder.countingCorollary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:56:41.826558+00:00
-- url     : https://prove2.me/submissions/40d9bb2f-a2b4-4b49-886e-a80d6df3dbb1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Counting
import Theorems.Thm_PrintedOrder_stBounds
import Theorems.Thm_PrintedOrder_stepTwoFrom
import Theorems.Thm_PrintedOrder_tiedFrom
import Theorems.Thm_PrintedOrder_stTreeAddsUp
import Theorems.Thm_SplitCount_endFrom


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
namespace PrintedOrder
theorem _root_.solution : CountingAgain := SplitCount.endFrom (tiedFrom (stepTwoFrom stTreeAddsUp stBounds))
end PrintedOrder
