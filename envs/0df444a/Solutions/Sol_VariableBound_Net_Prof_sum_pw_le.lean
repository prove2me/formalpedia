-- Prove2me | solution 1 for VariableBound.Net.Prof.sum_pw_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:38:07.610974+00:00
-- url     : https://prove2.me/submissions/da89f20a-297b-4da0-99b3-c01f7acc2e09

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_VariableBound_Net_Prof_card_links_le
import Theorems.Thm_VariableBound_Net_Prof_mem_tst
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_card_links_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, pw g n D P a b κ ≤ (k - 1 + κ) * (kP D P κ).card := by
  have e1 : ∀ b, ∀ a ∈ range b, pw g n D P a b κ = ∑ o ∈ kP D P κ, if linkB g n D o a b = true then 1 else 0 := by
    intro b a ha
    unfold pw kP
    rw [← card_filter, filter_filter]
    congr 1
    refine filter_congr fun o ho => ?_
    rw [mem_tst (mem_range.1 ha)]
    have := mem_range.1 (hP ho)
    tauto
  calc ∑ b ∈ range g, ∑ a ∈ range b, pw g n D P a b κ
      = ∑ b ∈ range g, ∑ a ∈ range b, ∑ o ∈ kP D P κ, (if linkB g n D o a b = true then 1 else 0) :=
        sum_congr rfl fun b _ => sum_congr rfl fun a ha => e1 b a ha
    _ ≤ ∑ b ∈ range g, ∑ a ∈ range g, ∑ o ∈ kP D P κ, (if linkB g n D o a b = true then 1 else 0) :=
        sum_le_sum fun b hb => sum_le_sum_of_subset (range_subset_range.2 (mem_range.1 hb).le)
    _ = ∑ o ∈ kP D P κ, ∑ a ∈ range g, ∑ b ∈ range g, (if linkB g n D o a b = true then 1 else 0) := by
        rw [sum_comm]
        rw [sum_congr rfl fun a _ => sum_comm]
        rw [sum_comm]
    _ = ∑ o ∈ kP D P κ, ((range g ×ˢ range g).filter fun p => linkB g n D o p.1 p.2 = true).card := by
        refine sum_congr rfl fun o _ => ?_
        rw [card_filter, sum_product]
    _ ≤ ∑ _o ∈ kP D P κ, (k - 1 + κ) := sum_le_sum fun o ho => by
        have := card_links_le hg h (mem_range.1 (hP (mem_filter.1 ho).1))
        rwa [(mem_filter.1 ho).2] at this
    _ = (k - 1 + κ) * (kP D P κ).card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
end VariableBound.Net.Prof
