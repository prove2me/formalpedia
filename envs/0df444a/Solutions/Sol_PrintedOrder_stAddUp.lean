-- Prove2me | solution 1 for PrintedOrder.stAddUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:17:02.803689+00:00
-- url     : https://prove2.me/submissions/9bec9f87-01ab-4ae2-9abb-0eb45fdef767

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_PrintedOrder_cntN_eq
import Theorems.Thm_PrintedOrder_card_some

set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
namespace PrintedOrder
theorem _root_.solution : StAddUp := by
  classical
  intro n ψ L hp hc
  rw [← card_some n L hp, cntN_eq]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => hc (ext b))
end PrintedOrder
