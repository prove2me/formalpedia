-- Prove2me | solution 1 for WidthK.Refine.pairwise_pairsK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:19:34.780981+00:00
-- url     : https://prove2.me/submissions/273db8ec-2fa9-40d4-a718-99815e5317ba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution (k : ℕ) : (pairsK k).Pairwise Before := by
  rw [pairsK, List.pairwise_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    rw [List.pairwise_reverse]
    exact (List.pairwise_lt_range (n := j)).imp fun {a b} hab => Or.inr ⟨rfl, hab⟩
  · refine (List.pairwise_lt_range (n := k + 1)).imp fun {a b} hab x hx y hy => ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
    exact Or.inl hab
end WidthK.Refine
