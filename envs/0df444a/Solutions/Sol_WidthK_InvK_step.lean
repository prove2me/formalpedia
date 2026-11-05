-- Prove2me | solution 1 for WidthK.InvK.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:19:13.551356+00:00
-- url     : https://prove2.me/submissions/6edf60e8-0cb1-4d28-97ea-2c3a7632ef96

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
import Theorems.Thm_WidthK_Step_notMem
import Theorems.Thm_WidthK_Step_red_union
import Theorems.Thm_WidthK_Step_lay_nextN_of_ne
import Theorems.Thm_WidthK_Step_lay_nextN_of_lt
import Theorems.Thm_WidthK_Step_lay_nextN_self
import Theorems.Thm_WidthK_Step_sum_nextA_of_le
import Theorems.Thm_WidthK_Step_sum_nextA_of_lt
import Theorems.Thm_WidthK_Step_card_lay_le
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
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}
namespace WidthK
namespace InvK
theorem _root_.solution (h : InvK d F N a) (hA : AddK d F A r) :
    InvK d (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) where
  red := reduced_red _
  sub := by
    rw [red_union h.red hA]
    exact union_subset_union_right (filter_subset_filter _ h.sub)
  deg := by
    intro i y
    by_cases hi : i = r
    · subst hi
      rw [lay_nextN_self h.red h.sub hA, filter_union]
      have h1 : ((lay N i).filter fun C => y ∈ C).card ≤ (Sparsify.over F i {y}).card := by
        apply card_le_card
        intro C hC
        obtain ⟨hCN, hyC⟩ := mem_filter.1 hC
        obtain ⟨hCN, hc⟩ := mem_filter.1 hCN
        exact mem_filter.2 ⟨h.sub hCN, hc, singleton_subset_iff.2 hyC⟩
      have := card_union_le (A.filter fun C => y ∈ C) ((lay N i).filter fun C => y ∈ C)
      have := hA.deg y
      omega
    · rw [lay_nextN_of_ne hA hi]
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (h.deg i y)
  acc := by
    intro i
    rcases lt_trichotomy i r with hi | hi | hi
    · rw [lay_nextN_of_lt hA hi, sum_nextA_of_le a _ hi.le]
      simpa only [nextA, if_neg hi.ne, Nat.add_zero] using h.acc i
    · subst hi
      rw [lay_nextN_self h.red h.sub hA, sum_nextA_of_le a _ le_rfl, card_union_of_disjoint]
      · have := h.acc i
        simp only [nextA, if_true]
        omega
      · rw [disjoint_left]
        intro C hCA hCN
        exact notMem h.red hA hCA (h.sub (mem_filter.1 hCN).1)
    · rw [lay_nextN_of_ne hA hi.ne', sum_nextA_of_lt a _ hi]
      have h1 := h.acc i
      have h2 := card_lay_le h hA i
      simp only [nextA, if_neg hi.ne', Nat.add_zero, Nat.mul_add]
      rw [Nat.mul_comm (d i) A.card]
      omega
end InvK
end WidthK
