-- Prove2me | solution 1 for SparsificationLemma.stCountOfExactlyOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:41.262685+00:00
-- url     : https://prove2.me/submissions/7b3462ec-d6aa-4858-b13b-c9dfd1a8d0b1

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
import Theorems.Thm_SparsificationLemma_exactlyOne_iff_countP
import Theorems.Thm_SparsificationLemma_cntN_eq_sum
import Theorems.Thm_SparsificationLemma_sum_cntN
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount
namespace SparsificationLemma
theorem _root_.solution : StCountOfExactlyOne := by
  intro n ψ Φ h
  rw [sum_cntN, cntN_eq_sum]
  exact Finset.sum_congr rfl fun a _ => ((exactlyOne_iff_countP (ext a) ψ Φ).1 (h (ext a))).symm
end SparsificationLemma
