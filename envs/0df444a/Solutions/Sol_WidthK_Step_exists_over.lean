-- Prove2me | solution 1 for WidthK.Step.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:14:19.386108+00:00
-- url     : https://prove2.me/submissions/3b44da2d-09dc-4633-9c25-1bf88e47548d

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
open WidthK.Step
namespace WidthK.Step
theorem _root_.solution (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) : ∃ C, C ∈ Sparsify.over F j H :=
  card_pos.1 (lt_of_lt_of_le (hθ _) hB.heart.2.2)
end WidthK.Step
