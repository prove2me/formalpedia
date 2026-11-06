-- Prove2me | solution 1 for SparsificationLemma.Gen.cntN_leafM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:59.955766+00:00
-- url     : https://prove2.me/submissions/f309e394-10b3-4102-95ec-e281ee06c2a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Gen
import Theorems.Thm_CountKSatRate_Leaf_sat_leafM_iff
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}
namespace SparsificationLemma.Gen
theorem _root_.solution {x : CNode} (hs : ∀ C ∈ x.2, C ∈ taut n ∨ ∃ l, C = [l]) : cntN n (leafM x) = cntN n (leafF x) := by
  rw [cntN, cntN]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ => CountKSatRate.Leaf.sat_leafM_iff hs _)
end SparsificationLemma.Gen
