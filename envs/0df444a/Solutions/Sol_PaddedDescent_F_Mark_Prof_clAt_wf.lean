-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.clAt_wf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:11:52.108358+00:00
-- url     : https://prove2.me/submissions/539221cd-fd24-43ee-a6eb-1e6659aabb91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {k n : ℕ} {Ls : List Fml} (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (clAt Ls e).2 ≠ [] ∧ (clAt Ls e).2.length ≤ k ∧ ∀ l ∈ (clAt Ls e).2, l.1 < n := by
  have hm : clAt Ls e ∈ cls Ls := by
    unfold clAt
    rw [List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  unfold cls at hm
  rw [List.mem_flatMap] at hm
  obtain ⟨i, hi, hm⟩ := hm
  rw [List.mem_map] at hm
  obtain ⟨C, hC, hCe⟩ := hm
  rw [← hCe]
  have hi' := List.mem_range.1 hi
  have hL : Ls.getD i [] ∈ Ls := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  exact h _ hL C hC
end PaddedDescent.F.Mark.Prof
