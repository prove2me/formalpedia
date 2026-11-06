-- Prove2me | solution 1 for PrintedOrder.stTreeAddsUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:55.650624+00:00
-- url     : https://prove2.me/submissions/805385bc-2b42-4665-b764-c2bc10a338dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_PrintedOrder_stAddUp
import Theorems.Thm_PrintedOrder_stCovered
import Theorems.Thm_PrintedOrder_stRootSame
import Theorems.Thm_PrintedOrder_treeAddsUpFrom
import Theorems.Thm_SplitCount_stDisjointLeaves


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
namespace PrintedOrder
theorem _root_.solution : StTreeAddsUp := treeAddsUpFrom stDisjointLeaves stCovered stRootSame stAddUp
end PrintedOrder
