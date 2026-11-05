-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.sum_pw_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:23:52.5095+00:00
-- url     : https://prove2.me/submissions/948aded7-b3e8-4aa5-8e7b-482cc7976d81

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_card_links_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (i : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, pw g n Ls P a' a i ≤ (k - 1) * (layP Ls P i).card := by
  have e1 : ∀ a, ∀ a' ∈ range a, pw g n Ls P a' a i = ∑ e ∈ layP Ls P i, if linkB g n Ls e a' a = true then 1 else 0 := by
    intro a a' ha'
    unfold pw layP
    rw [← card_filter, filter_filter]
    congr 1
    refine filter_congr fun e he => ?_
    rw [mem_tst (mem_range.1 ha')]
    have := mem_range.1 (hP he)
    tauto
  calc ∑ a ∈ range g, ∑ a' ∈ range a, pw g n Ls P a' a i
      = ∑ a ∈ range g, ∑ a' ∈ range a, ∑ e ∈ layP Ls P i, (if linkB g n Ls e a' a = true then 1 else 0) :=
        sum_congr rfl fun a _ => sum_congr rfl fun a' ha' => e1 a a' ha'
    _ ≤ ∑ a ∈ range g, ∑ a' ∈ range g, ∑ e ∈ layP Ls P i, (if linkB g n Ls e a' a = true then 1 else 0) :=
        sum_le_sum fun a ha => sum_le_sum_of_subset (range_subset_range.2 (mem_range.1 ha).le)
    _ = ∑ e ∈ layP Ls P i, ∑ a' ∈ range g, ∑ a ∈ range g, (if linkB g n Ls e a' a = true then 1 else 0) := by
        rw [sum_comm]
        rw [sum_congr rfl fun a' _ => sum_comm]
        rw [sum_comm]
    _ = ∑ e ∈ layP Ls P i, ((range g ×ˢ range g).filter fun p => linkB g n Ls e p.1 p.2 = true).card := by
        refine sum_congr rfl fun e _ => ?_
        rw [card_filter, sum_product]
    _ ≤ ∑ _e ∈ layP Ls P i, (k - 1) := sum_le_sum fun e he => card_links_le hg h (mem_range.1 (hP (mem_filter.1 he).1))
    _ = (k - 1) * (layP Ls P i).card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
end PaddedDescent.F.Mark.Prof
