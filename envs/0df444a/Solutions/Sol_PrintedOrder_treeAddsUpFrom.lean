-- Prove2me | solution 1 for PrintedOrder.treeAddsUpFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:53.724603+00:00
-- url     : https://prove2.me/submissions/b09752f8-9522-46a4-bb8f-4ce9d82559d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitCount_leaves_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
namespace PrintedOrder
theorem _root_.solution : SplitCount.StDisjointLeaves → StCovered → StRootSame → StAddUp → StTreeAddsUp := by
  intro hD hC hR hA θ k d n ψ
  have cP : ∀ y : CNode, stepPlain (stepC θ k) (List.replicate n (), y) =
      (stepC θ k y).map fun lh => ((List.replicate n (), lh.1), (List.replicate n (), lh.2)) := fun _ => rfl
  have hP : rootPlain (List.replicate n (), ψ) = (List.replicate n (), ((rootP ψ, []) : CNode)) := rfl
  have key := hA n ψ ((leaves (stepC θ k) d (rootP ψ, [])).map leafF) (List.pairwise_map.2 (hD θ k d _)) fun a => by
    rw [← hR (List.replicate n ()) ψ a]
    refine (hC θ k d _ a).trans ⟨fun ⟨y, hy, h⟩ => ⟨leafF y, List.mem_map_of_mem hy, h⟩, fun ⟨z, hz, h⟩ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact ⟨y, hy, h⟩
  rw [hP, leaves_map (f := Prod.mk (List.replicate n ())) cP, List.map_map, key, List.map_map]
  rfl
end PrintedOrder
