-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.sum_length_tst_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:11.956207+00:00
-- url     : https://prove2.me/submissions/7203db59-b5b2-432d-b7ec-7558ed0422b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Size_length_filter_eq_card
import Theorems.Thm_PaddedDescent_F_Mark_Size_countP_cls
import Theorems.Thm_PaddedDescent_F_Mark_Size_card_links_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
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
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_filter_range
attribute [local fun_prop] Groundwork.PolyT.length
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution (k i : ℕ) (hk : ∀ C ∈ Ls.getD i [], C.length ≤ k) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n Ls p.1 p.2 i).length else 0) ≤ (k - 1) * (Ls.getD i []).length := by
  have h1 : ∀ p : ℕ × ℕ, (if p.1 < p.2 then (tst g n Ls p.1 p.2 i).length else 0) =
      ∑ e ∈ range (cls Ls).length, if (clAt Ls e).1 = i ∧ linkB g n Ls e p.1 p.2 = true then 1 else 0 := by
    intro p
    rw [← card_filter]
    split_ifs with hp
    · rw [tst, length_filter_eq_card, min_eq_left hp.le, max_eq_right hp.le]
      congr 1
      ext e
      simp
    · symm
      exact card_eq_zero.2 (filter_eq_empty_iff.2 fun e _ he => hp (linkB_iff.1 he.2).1)
  rw [sum_congr rfl fun p _ => h1 p, sum_comm]
  have h2 : ∀ e ∈ range (cls Ls).length, (∑ p ∈ (range g) ×ˢ (range g), if (clAt Ls e).1 = i ∧ linkB g n Ls e p.1 p.2 = true then 1 else 0) ≤
      if (clAt Ls e).1 = i then k - 1 else 0 := by
    intro e he
    split_ifs with hi
    · simp only [hi, true_and]
      rw [← card_filter]
      refine (card_links_le e).trans (Nat.sub_le_sub_right (hk _ ?_) 1)
      have hm : clAt Ls e ∈ cls Ls := by
        rw [clAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (mem_range.1 he), Option.getD_some]
        exact List.getElem_mem _
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hm
      obtain ⟨C, hC, hCe⟩ := List.mem_map.1 hj
      rw [← hCe] at hi ⊢
      exact hi ▸ hC
    · simp [hi]
  refine (sum_le_sum h2).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm]
  refine Nat.mul_le_mul_left _ (le_of_eq ?_)
  rw [← countP_cls, ← Deg.length_filter_range (cls Ls) (0, []) fun c => c.1 == i, length_filter_eq_card]
  congr 1
  ext e
  simp [clAt]
end PaddedDescent.F.Mark.Size
