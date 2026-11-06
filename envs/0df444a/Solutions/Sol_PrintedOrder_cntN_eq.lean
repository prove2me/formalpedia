-- Prove2me | solution 1 for PrintedOrder.cntN_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:49.503197+00:00
-- url     : https://prove2.me/submissions/694e253b-b6b0-4f39-9d20-c2dd3eae2725

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
open Classical
namespace PrintedOrder
theorem _root_.solution (n : ℕ) (y : Fml) : cntN n y = (Finset.univ.filter fun b : Fin n → Bool => Holds (ext b) y).card := by
  unfold cntN Holds
  congr!
end PrintedOrder
