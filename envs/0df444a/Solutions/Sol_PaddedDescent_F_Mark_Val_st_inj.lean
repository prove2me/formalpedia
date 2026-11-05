-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.st_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:43.663201+00:00
-- url     : https://prove2.me/submissions/738ea1f3-2406-46df-a177-ec8f3f5f9628

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_tchB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_mem_tch
import Theorems.Thm_PaddedDescent_F_Mark_Val_getD_st_lt
import Theorems.Thm_PaddedDescent_F_Mark_Val_mark_st
import Theorems.Thm_PaddedDescent_F_Mark_Val_div_qv_lt
import Theorems.Thm_PaddedDescent_F_Mark_Val_qv_pos
import Theorems.Thm_PaddedDescent_F_Mark_Val_lit_lt
import Theorems.Thm_PaddedDescent_F_Mark_Val_exists_lit
import Theorems.Thm_PaddedDescent_F_Mark_Val_ext_of_lt
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hg : 0 < g) (hw : WfL k n Ls) {σ σ' : Fin n → Bool} {P P' : Finset ℕ}
    (hP : P ⊆ Finset.range (cls Ls).length) (hP' : P' ⊆ Finset.range (cls Ls).length)
    (h : (fun a : Fin g => st g n Ls (ext σ) P a) = fun a : Fin g => st g n Ls (ext σ') P' a) : σ = σ' ∧ P = P' := by
  constructor
  · funext x
    have hq : 0 < qv g n := qv_pos hg (by have := x.2; omega)
    have h1 := congrFun h ⟨x.1 / qv g n, div_qv_lt hg x.2⟩
    have h2 := congrArg (fun l => l.getD (x.1 % qv g n) false) h1
    simp only [getD_st_lt _ _ _ (Nat.mod_lt _ hq), Nat.div_add_mod'] at h2
    rwa [ext_of_lt x.2, ext_of_lt x.2] at h2
  · ext e
    by_cases he : e < (cls Ls).length
    · obtain ⟨l, hl⟩ := exists_lit hw he
      have hlt := lit_lt hw he hl
      have ht : e ∈ tch g n Ls (l.1 / qv g n) := mem_tch.2 ⟨he, tchB_iff.2 ⟨l, hl, rfl⟩⟩
      have h1 := congrFun h ⟨l.1 / qv g n, div_qv_lt hg hlt⟩
      have h2 := congrArg (fun z => mark g n Ls (l.1 / qv g n) z e) h1
      simp only [mark_st _ _ ht] at h2
      simpa using h2
    · exact ⟨fun h => absurd (Finset.mem_range.1 (hP h)) he, fun h => absurd (Finset.mem_range.1 (hP' h)) he⟩
end PaddedDescent.F.Mark.Val
