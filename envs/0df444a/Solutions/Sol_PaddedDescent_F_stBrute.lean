-- Prove2me | solution 1 for PaddedDescent.F.stBrute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:45:22.736037+00:00
-- url     : https://prove2.me/submissions/c650463b-b532-4eed-a1a7-d5666380a751

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_F_Descend
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_query0_eq
import Theorems.Thm_Groundwork_sum_blocks_pairs
import Theorems.Thm_Groundwork_sum_toWord
import Theorems.Thm_PaddedDescent_F_prodL_eq
import Theorems.Thm_PaddedDescent_F_sumF_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog Finset Lists
namespace PaddedDescent.F
theorem _root_.solution : StBrute := by
  intro pad K I h
  unfold bruteF zval Inst.ZW
  rw [sumF_eq h, ← sum_blocks_pairs K I.1.length [] fun Λ => ∏ v, instOf (K := K) I.2 v (star Λ v), ← sum_toWord]
  refine sum_congr rfl fun y _ => ?_
  rw [prodL_eq, prod_range]
  refine prod_congr rfl fun v _ => ?_
  rw [query0_eq]
  rfl
end PaddedDescent.F
