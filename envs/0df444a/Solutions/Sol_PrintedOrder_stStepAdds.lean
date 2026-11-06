-- Prove2me | solution 1 for PrintedOrder.stStepAdds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:26:09.091687+00:00
-- url     : https://prove2.me/submissions/0fa1b457-162d-4241-9d27-74812f8d99c9

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
import Theorems.Thm_PrintedOrder_stepAddsFrom
import Theorems.Thm_SplitCount_stDisjoint


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
namespace PrintedOrder
theorem _root_.solution : StStepAdds := stepAddsFrom stDisjoint stAddUp
end PrintedOrder
