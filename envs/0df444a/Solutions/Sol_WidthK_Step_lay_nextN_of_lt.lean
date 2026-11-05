-- Prove2me | solution 1 for WidthK.Step.lay_nextN_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:15:35.536598+00:00
-- url     : https://prove2.me/submissions/d899b16f-91cc-4341-86b8-b7c8ce176b10

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
import Theorems.Thm_WidthK_Step_lay_nextN_of_ne
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open WidthK.Step
variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}
namespace WidthK.Step
theorem _root_.solution (hA : AddK d F A r) {i : ℕ} (hi : i < r) : lay (nextN N A) i = lay N i := by
  rw [lay_nextN_of_ne hA hi.ne, filter_eq_self]
  intro C hC D hD hDC
  have := card_le_card hDC
  rw [hA.size D hD, (mem_filter.1 hC).2] at this
  omega
end WidthK.Step
