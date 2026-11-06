-- Prove2me | solution 1 for VariableBound.Net.Prof.card_links_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:05.101982+00:00
-- url     : https://prove2.me/submissions/6dcfaf1b-f1d0-4920-af73-8b48291e21ac

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
import Theorems.Thm_VariableBound_Net_Prof_mem_tset
import Theorems.Thm_VariableBound_Net_Prof_tset_nonempty
import Theorems.Thm_VariableBound_Net_Prof_card_tset_le
import Theorems.Thm_VariableBound_Net_Prof_linkB_iff
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_card_tset_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tset
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tset_nonempty
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    ((range g ×ˢ range g).filter fun p => linkB g n D o p.1 p.2 = true).card ≤ k - 1 + (obAt D o).1 := by
  have hne := tset_nonempty hg h ho
  have h0 := min'_mem _ hne
  have hcard : ((tset g n D o).erase ((tset g n D o).min' hne)).card ≤ k - 1 + (obAt D o).1 := by
    rw [card_erase_of_mem h0]
    have := card_tset_le (g := g) h ho
    omega
  refine le_trans (card_le_card_of_injOn (fun p => p.2) ?_ ?_) hcard
  · intro p hp
    have hp' := mem_filter.1 (mem_coe.1 hp)
    obtain ⟨h1, h2, h3, _⟩ := linkB_iff.1 hp'.2
    have hp1 := mem_product.1 hp'.1
    refine mem_coe.2 (mem_erase.2 ⟨?_, mem_tset.2 ⟨mem_range.1 hp1.2, h3⟩⟩)
    intro heq
    have := min'_le _ p.1 (mem_tset.2 ⟨mem_range.1 hp1.1, h2⟩)
    simp only at heq
    omega
  · intro p hp p' hp' heq
    have hq := mem_filter.1 (mem_coe.1 hp)
    have hq' := mem_filter.1 (mem_coe.1 hp')
    obtain ⟨h1, h2, _, h4⟩ := linkB_iff.1 hq.2
    obtain ⟨h1', h2', _, h4'⟩ := linkB_iff.1 hq'.2
    have hr := mem_product.1 hq.1
    have hr' := mem_product.1 hq'.1
    simp only at heq
    have h5 : p.1 = p'.1 := by
      rcases Nat.lt_trichotomy p.1 p'.1 with hlt | heq' | hlt
      · have := h4 p'.1 (mem_range.1 hr'.1) hlt (by omega)
        rw [h2'] at this
        exact absurd this (by simp)
      · exact heq'
      · have := h4' p.1 (mem_range.1 hr.1) hlt (by omega)
        rw [h2] at this
        exact absurd this (by simp)
    exact Prod.ext h5 heq
end VariableBound.Net.Prof
