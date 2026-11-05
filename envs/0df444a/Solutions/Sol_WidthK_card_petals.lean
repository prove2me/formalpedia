-- Prove2me | solution 1 for WidthK.card_petals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:14:42.361567+00:00
-- url     : https://prove2.me/submissions/aee53e0b-9631-4848-9646-ab8bc666637e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
namespace WidthK
theorem _root_.solution (F : Finset (Finset α)) (j : ℕ) (H : Finset α) :
    (petals F j H).card = (Sparsify.over F j H).card := by
  refine card_image_of_injOn ?_
  intro C hC D hD hCD
  have hHC := (mem_filter.1 (mem_coe.1 hC)).2.2
  have hHD := (mem_filter.1 (mem_coe.1 hD)).2.2
  have hCD' : C \ H = D \ H := hCD
  rw [← sdiff_union_of_subset hHC, ← sdiff_union_of_subset hHD, hCD']
end WidthK
