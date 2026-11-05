-- Prove2me | solution 1 for PaddedDescent.F.Mark.Deg.card_filter_mem_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:15.573194+00:00
-- url     : https://prove2.me/submissions/0fe8e9a7-546b-40ce-9d54-ef198c86a95b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_PaddedDescent_F_Mark_Deg_card_filter_mem_le_one
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_WidthK_Step_card_filter_mem_le_one
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}
namespace PaddedDescent.F.Mark.Deg
theorem _root_.solution (hθ : ∀ i, 0 < θ i) (h : WidthK.Leaf θ k F) (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) (y : α) :
    (F.filter fun C => y ∈ C).card ≤ ∑ i ∈ range k, θ i := by
  have hd : ∀ i < k, ((lay F (i + 1)).filter fun C => y ∈ C).card ≤ θ i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact (card_filter_mem_le_one (fun C hC => (mem_filter.1 hC).2) y).trans (hθ 0)
    · by_contra hc
      refine h (i + 1) hi {y} ⟨singleton_nonempty y, by rw [card_singleton]; omega, ?_⟩
      rw [card_singleton, Nat.add_sub_cancel]
      simpa only [lay, Sparsify.over, filter_filter, singleton_subset_iff] using (not_le.1 hc).le
  have hsub : (F.filter fun C => y ∈ C) ⊆ (range k).biUnion fun i => (lay F (i + 1)).filter fun C => y ∈ C := by
    intro C hC
    obtain ⟨hCF, hy⟩ := mem_filter.1 hC
    obtain ⟨h1, h2⟩ := hF C hCF
    exact mem_biUnion.2 ⟨C.card - 1, mem_range.2 (by omega), mem_filter.2 ⟨mem_filter.2 ⟨hCF, by omega⟩, hy⟩⟩
  calc (F.filter fun C => y ∈ C).card ≤ ((range k).biUnion fun i => (lay F (i + 1)).filter fun C => y ∈ C).card := card_le_card hsub
    _ ≤ ∑ i ∈ range k, ((lay F (i + 1)).filter fun C => y ∈ C).card := card_biUnion_le
    _ ≤ ∑ i ∈ range k, θ i := sum_le_sum fun i hi => hd i (mem_range.1 hi)
end PaddedDescent.F.Mark.Deg
