-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.st_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:02:52.710645+00:00
-- url     : https://prove2.me/submissions/ad2a8303-d056-41ce-9982-8f47893449d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_PaddedDescent_F_Mark_Val_mem_tch
import Theorems.Thm_PaddedDescent_F_Mark_Val_tst_comm
import Theorems.Thm_PaddedDescent_F_Mark_Val_getD_st_lt
import Theorems.Thm_PaddedDescent_F_Mark_Val_mark_st
import Theorems.Thm_PaddedDescent_F_Mark_Val_str_st
import Theorems.Thm_PaddedDescent_F_Mark_Val_base_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_vio_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_qv_pos
import Theorems.Thm_PaddedDescent_F_Mark_Val_lit_lt
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hg : 0 < g) (hw : WfL k n Ls) {σ : ℕ → Bool} (hσ : ∀ x, n ≤ x → σ x = false) {P : Finset ℕ}
    (hP : P ⊆ vset σ Ls) : Gd g n Ls fun a => st g n Ls σ P a := by
  refine ⟨fun a => base_iff.2 ⟨fun r hr => ?_, fun e he => ?_⟩, fun a a' _ i _ => ?_⟩
  · by_cases h : a.val * qv g n + r < n
    · exact Or.inl h
    · exact Or.inr (by rw [getD_st_lt σ P a hr]; exact hσ _ (not_lt.1 h))
  · rw [mark_st σ P he]
    by_cases heP : e ∈ P
    · refine Or.inr fun l hl => ?_
      by_cases hla : l.1 / qv g n = a
      · refine Or.inr ?_
        have hlt := lit_lt hw (mem_tch.1 he).1 hl
        have hq : 0 < qv g n := qv_pos hg (by omega)
        rw [getD_st_lt σ P a (Nat.mod_lt _ hq), ← hla, Nat.div_add_mod']
        exact vio_iff.1 (Finset.mem_filter.1 (hP heP)).2 l hl
      · exact Or.inl hla
    · exact Or.inl (by simpa using heP)
  · rw [str_st, str_st, tst_comm]
end PaddedDescent.F.Mark.Val
