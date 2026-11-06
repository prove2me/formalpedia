-- Prove2me | solution 1 for VariableBound.Net.SizeB.card_marked_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:37.338999+00:00
-- url     : https://prove2.me/submissions/3cc53daa-c371-46f3-b790-55fbe5cbfe3d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeB
import Theorems.Thm_VariableBound_Net_SizeB_mem_tch
import Theorems.Thm_VariableBound_Net_SizeB_nodup_tch
import Theorems.Thm_VariableBound_Net_SizeB_mem_tst
import Theorems.Thm_VariableBound_Net_SizeB_nodup_tst
import Theorems.Thm_VariableBound_Net_SizeB_length_filter_eq_card
import Theorems.Thm_VariableBound_Net_SizeB_own_or_test
import Theorems.Thm_VariableBound_Net_SizeB_okD_spec
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_Unary_comp
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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tst
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.count
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
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}
namespace VariableBound.Net.SizeB
theorem _root_.solution {a : ℕ} {z : List Bool} (ha : a < g) (h : okD g n D y a z = true) :
    #(mk g n D a z) ≤ mu g D y a a 1 + ∑ b ∈ (range g).erase a, mu g D y a b 1 := by
  obtain ⟨h1, h2⟩ := okD_spec h
  have hO : mu g D y a a 1 = #((range (objs D).length).filter fun o => tchB g n D a o = true ∧ (obAt D o).1 = 1 ∧ ownB g n D o a = true ∧ mark g n D a z o = true) := by
    rw [← h1 1 (by norm_num)]
    refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
    simp only [mem_tch, Bool.and_eq_true, beq_iff_eq, mem_filter, mem_range]
    tauto
  have hT : ∀ b ∈ (range g).erase a, mu g D y a b 1 = #((range (objs D).length).filter fun o => o ∈ tst g n D a b 1 ∧ mark g n D a z o = true) := by
    intro b hb
    obtain ⟨hne, hb⟩ := mem_erase.1 hb
    rw [← h2 b (mem_range.1 hb) hne 1 (by norm_num), str, List.count, List.countP_map, List.countP_eq_length_filter]
    refine length_filter_eq_card (nodup_tst a b 1) _ _ fun e => ?_
    simp only [Function.comp, beq_iff_eq, mem_filter, mem_range]
    exact ⟨fun hh => ⟨(mem_tst.1 hh.1).1, hh⟩, fun hh => hh.2⟩
  rw [hO, sum_congr rfl hT]
  refine le_trans (card_le_card ?_) ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  intro o ho
  obtain ⟨h3, h4, h5, h6⟩ := mem_filter.1 ho
  rcases own_or_test h4 with h7 | ⟨c, hc, h7⟩
  · exact mem_union_left _ (mem_filter.2 ⟨h3, h4, h5, h7, h6⟩)
  · refine mem_union_right _ (mem_biUnion.2 ⟨c, mem_erase.2 ⟨hc.ne, mem_range.2 (hc.trans ha)⟩, mem_filter.2 ⟨h3, mem_tst.2 ⟨mem_range.1 h3, h5, ?_⟩, h6⟩⟩)
    rwa [min_eq_right hc.le, max_eq_left hc.le]
end VariableBound.Net.SizeB
