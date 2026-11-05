-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.U_markN_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:40.422942+00:00
-- url     : https://prove2.me/submissions/c1db384e-1515-4f1c-9552-f25464847b92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_length_tst_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Size_mcap_comm
import Theorems.Thm_PaddedDescent_F_Mark_Size_adm_iff
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_erase_fin
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_erase_eq_two_mul
import Theorems.Thm_PaddedDescent_F_Mark_Size_ceil_le_succ
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_div_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_lt_eq_sum_product
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
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
theorem _root_.solution {gu nu βu bu : U} {w y k : ℕ} (h : adm k gu.length nu.length w Ls y = true) (hk : ∀ L ∈ Ls, ∀ C ∈ L, C.length ≤ k) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U ≤
      2 * ∑ i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = gu.length := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = nu.length := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = βu.length := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = bu.length := ⟨_, rfl⟩
  have hU : (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U = ∑ a ∈ range g, ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a' := by
    subst hg hn hβ hb
    simp only [Network.U, markN, markF]
    rw [← Fin.sum_univ_eq_sum_range fun a => ∑ a' ∈ (range gu.length).erase a, mcap gu.length nu.length βu.length bu.length Ls y a a']
    exact sum_congr rfl fun a _ => sum_erase_fin a fun a' => mcap gu.length nu.length βu.length bu.length Ls y a.val a'
  rw [← hg, ← hn] at h
  rw [hU, ← hg, ← hβ, ← hb, sum_erase_eq_two_mul _ (mcap_comm β b y)]
  refine Nat.mul_le_mul_left 2 ?_
  simp only [mcap, sum_map_range]
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_le_sum fun i hi => ?_
  simp only [sum_add_distrib]
  have hi' := mem_range.1 hi
  refine Nat.add_le_add ?_ ?_
  · have h2 := (adm_iff.1 h i hi').2.1
    simp only [sum_map_range] at h2
    simp only [← sum_mul]
    exact Nat.mul_le_mul_right _ h2
  · calc ∑ a ∈ range g, ∑ a' ∈ range a, ((tst g n Ls a' a i).length + b - 1) / b
        ≤ ∑ a ∈ range g, ∑ a' ∈ range a, ((tst g n Ls a' a i).length / b + 1) :=
          sum_le_sum fun a _ => sum_le_sum fun a' _ => ceil_le_succ b _
      _ = ∑ a ∈ range g, ∑ a' ∈ range a, (tst g n Ls a' a i).length / b + ∑ a ∈ range g, a := by
          simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
      _ ≤ (k - 1) * (Ls.getD i []).length / b + g * g := by
          refine Nat.add_le_add ?_ ?_
          · refine ((sum_le_sum fun a _ => sum_div_le _ _ b).trans (sum_div_le _ _ b)).trans (Nat.div_le_div_right ?_)
            rw [sum_lt_eq_sum_product fun a' a => (tst g n Ls a' a i).length]
            refine sum_length_tst_le k i fun C hC => hk _ ?_ C hC
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
            exact List.getElem_mem _
          · calc ∑ a ∈ range g, a ≤ ∑ _a ∈ range g, g := sum_le_sum fun a ha => (mem_range.1 ha).le
              _ = g * g := by simp
end PaddedDescent.F.Mark.Size
