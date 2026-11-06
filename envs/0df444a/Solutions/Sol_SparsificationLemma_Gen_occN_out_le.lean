-- Prove2me | solution 1 for SparsificationLemma.Gen.occN_out_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:20.754239+00:00
-- url     : https://prove2.me/submissions/80bdfe73-bac8-49f7-8a33-cff5a71fc4ee

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
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}
namespace SparsificationLemma.Gen
theorem _root_.solution (x : CNode) (v : ℕ) : occN (out x) v ≤ occN (leafM x) v :=
  ((List.dedup_sublist (leafM x)).filter _).length_le
end SparsificationLemma.Gen
