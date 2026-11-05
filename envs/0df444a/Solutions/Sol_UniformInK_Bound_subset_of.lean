-- Prove2me | solution 1 for UniformInK.Bound.subset_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:20:44.681988+00:00
-- url     : https://prove2.me/submissions/1ef14ef3-4045-469f-9b32-8d3c458fa2ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}
namespace UniformInK.Bound
theorem _root_.solution (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) : ∀ C ∈ F, C ⊆ U := by
  intro C hC
  obtain ⟨C', hC', hsub, -⟩ := h.1 C hC
  exact hsub.trans (hφ C' hC')
end UniformInK.Bound
