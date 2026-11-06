-- Prove2me | solution 1 for UniformInK.Step.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:35.538146+00:00
-- url     : https://prove2.me/submissions/e873133b-b104-4579-9d32-8346107de367

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_UniformInK_Step_toAddK
import Theorems.Thm_UniformInK_Step_wsum_nextA_of_le
import Theorems.Thm_UniformInK_Step_wsum_nextA_of_lt
import Theorems.Thm_UniformInK_Step_card_lay_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Sparsify_reduced_red
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
import Theorems.Thm_WidthK_Step_card_lay_le
import Theorems.Thm_WidthK_Step_lay_nextN_of_lt
import Theorems.Thm_WidthK_Step_lay_nextN_of_ne
import Theorems.Thm_WidthK_Step_lay_nextN_self
import Theorems.Thm_WidthK_Step_notMem
import Theorems.Thm_WidthK_Step_red_union
attribute [local fun_prop] Groundwork.PolyT.all
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
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Step
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}
namespace UniformInK.Step
theorem _root_.solution (h : InvU θ F N a) (hA : AddU θ F A r) :
    InvU θ (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) where
  red := reduced_red _
  sub := by
    rw [WidthK.Step.red_union h.red (toAddK hA)]
    exact union_subset_union_right (filter_subset_filter _ h.sub)
  deg := by
    intro i Y hY hYi
    by_cases hi : i = r
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), filter_union]
      have h1 : ((lay N i).filter fun C => Y ⊆ C).card ≤ (Sparsify.over F i Y).card := by
        apply card_le_card
        intro C hC
        obtain ⟨hCN, hYC⟩ := mem_filter.1 hC
        obtain ⟨hCN, hc⟩ := mem_filter.1 hCN
        exact mem_filter.2 ⟨h.sub hCN, hc, hYC⟩
      have := card_union_le (A.filter fun C => Y ⊆ C) ((lay N i).filter fun C => Y ⊆ C)
      have := hA.deg Y hY hYi
      omega
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi]
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (h.deg i Y hY hYi)
  acc := by
    intro i
    rcases lt_trichotomy i r with hi | hi | hi
    · rw [WidthK.Step.lay_nextN_of_lt (toAddK hA) hi, wsum_nextA_of_le _ a _ hi.le]
      simpa only [nextA, if_neg hi.ne, Nat.add_zero] using h.acc i
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), wsum_nextA_of_le _ a _ le_rfl, card_union_of_disjoint]
      · have := h.acc i
        simp only [nextA, if_true]
        omega
      · rw [disjoint_left]
        intro C hCA hCN
        exact WidthK.Step.notMem h.red (toAddK hA) hCA (h.sub (mem_filter.1 hCN).1)
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi.ne', wsum_nextA_of_lt _ a _ hi]
      have h1 := h.acc i
      have h2 := card_lay_le h hA hi.le
      simp only [nextA, if_neg hi.ne', Nat.add_zero]
      rw [Nat.mul_comm A.card] at h2
      omega
end UniformInK.Step
