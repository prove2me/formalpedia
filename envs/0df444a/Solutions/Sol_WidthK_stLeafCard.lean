-- Prove2me | solution 1 for WidthK.stLeafCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:19.916033+00:00
-- url     : https://prove2.me/submissions/227fedb9-5c94-4973-b976-8473b53dba69

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
import Theorems.Thm_WidthK_Leaf_card_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
namespace WidthK
theorem _root_.solution : StLeafCard := by
  intro α _ θ k n F U hθ hU hF h
  have := h.card_le hθ hU (fun C hC => (hF C hC).1) fun C hC => ⟨card_pos.2 (hF C hC).2.1, (hF C hC).2.2⟩
  calc F.card ≤ 2 * n * ∑ i ∈ range k, θ i := this
    _ = (2 * ∑ j ∈ range k, θ j) * n := by ring
end WidthK
