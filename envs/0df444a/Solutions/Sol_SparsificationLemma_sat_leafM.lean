-- Prove2me | solution 1 for SparsificationLemma.sat_leafM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:43:23.252206+00:00
-- url     : https://prove2.me/submissions/24f95cf1-f467-4d33-b365-94d4650c82aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto
import Definitions.Def_SparsificationLemma_One
import Theorems.Thm_CountKSatRate_Leaf_sat_leafM_iff
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount
namespace SparsificationLemma
theorem _root_.solution (b : ℕ → Bool) {x : CNode} (hx : ∀ C ∈ x.2, ∃ l, C = [l]) : Sat b (leafM x) ↔ Sat b (leafF x) :=
  Leaf.sat_leafM_iff (n := 0) (fun C hC => Or.inr (hx C hC)) b
end SparsificationLemma
