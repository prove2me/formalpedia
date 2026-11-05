-- Prove2me | solution 1 for WidthK.Refine.exists_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:19:31.020443+00:00
-- url     : https://prove2.me/submissions/86e8b512-c66f-4632-8b0f-a2f58e03e61d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_maskP_nil_left
import Theorems.Thm_WidthK_Refine_maskP_nil_right
import Theorems.Thm_WidthK_Refine_maskP_cons_true
import Theorems.Thm_WidthK_Refine_maskP_cons_false
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
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
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {k : ℕ} {C H : PCl} (hC : C.length ≤ k) (hH : H.Sublist C) : ∃ m ∈ masks k, maskP m C = H := by
  induction k generalizing C H with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hC)
    obtain rfl := List.sublist_nil.1 hH
    exact ⟨[], by simp [masks], maskP_nil_left _⟩
  | succ k ih =>
    cases C with
    | nil =>
      obtain rfl := List.sublist_nil.1 hH
      obtain ⟨m, hm, -⟩ := ih (C := []) (H := []) (Nat.zero_le _) (List.Sublist.refl _)
      exact ⟨false :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, maskP_nil_right _⟩
    | cons a C =>
      have hC' : C.length ≤ k := by simpa using hC
      cases hH with
      | cons _ h =>
        obtain ⟨m, hm, e⟩ := ih hC' h
        exact ⟨false :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, by rw [maskP_cons_false, e]⟩
      | cons_cons _ h =>
        obtain ⟨m, hm, e⟩ := ih hC' h
        exact ⟨true :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, by rw [maskP_cons_true, e]⟩
end WidthK.Refine
