-- Prove2me | solution 1 for P2M_WidthK_SetAlg_red_union__1cb354c1de8b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:14:49.818746+00:00
-- url     : https://prove2.me/submissions/54d22b6d-c003-4cdd-9bfa-4f4afd93c348

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
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
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
namespace WidthK.SetAlg
theorem _root_.solution {F A : Finset (Finset α)} (hF : Reduced F) (hss : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C)
    (hanti : ∀ D ∈ A, ∀ E ∈ A, D ⊆ E → D = E) : red (F ∪ A) = A ∪ F.filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by
  ext C
  simp only [red, mem_filter, mem_union]
  constructor
  · rintro ⟨hC, hmin⟩
    by_cases hCA : C ∈ A
    · exact Or.inl hCA
    · refine Or.inr ⟨hC.resolve_right hCA, fun D hD hDC => hCA ?_⟩
      rw [← hmin D (Or.inr hD) hDC]; exact hD
  · rintro (hCA | ⟨hCF, hno⟩)
    · refine ⟨Or.inr hCA, ?_⟩
      rintro D (hD | hD) hDC
      · obtain ⟨C', hC', hCC'⟩ := hss C hCA
        have := hF C' hC' D hD (hDC.trans hCC'.subset)
        subst this
        exact absurd hDC hCC'.2
      · exact hanti D hD C hCA hDC
    · refine ⟨Or.inl hCF, ?_⟩
      rintro D (hD | hD) hDC
      · exact hF C hCF D hD hDC
      · exact absurd hDC (hno D hD)
end WidthK.SetAlg
