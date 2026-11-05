-- Prove2me | solution 1 for WidthK.Step.card_of_mem_petals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:14:29.067301+00:00
-- url     : https://prove2.me/submissions/a3e139c4-2231-4899-b0e3-5eb9b9fbdc92

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
theorem _root_.solution {Q : Finset α} (hQ : Q ∈ petals F j H) : Q.card = j - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
  obtain ⟨-, hc, hHC⟩ := mem_filter.1 hC
  rw [card_sdiff_of_subset hHC, hc]
end WidthK.Step
