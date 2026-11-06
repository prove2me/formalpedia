-- Prove2me | solution 1 for P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:35.489977+00:00
-- url     : https://prove2.me/submissions/324f8787-1b73-453f-9b8f-448f26de4ae3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_VariableBound_Net_Tests_linkB_iff
import Theorems.Thm_VariableBound_Net_Tests_length_filter_eq_card
import Theorems.Thm_VariableBound_Net_Tests_card_links_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_card_links_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
import Theorems.Thm_VariableBound_Net_Basic_clOf_wf
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
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (hW : WfD k n D) (κ : ℕ) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n D p.1 p.2 κ).length else 0) ≤
      (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by
  have h1 : ∀ p : ℕ × ℕ, (if p.1 < p.2 then (tst g n D p.1 p.2 κ).length else 0) =
      ∑ e ∈ range (objs D).length, if (obAt D e).1 = κ ∧ linkB g n D e p.1 p.2 = true then 1 else 0 := by
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
  have h2 : ∀ e ∈ range (objs D).length, (∑ p ∈ (range g) ×ˢ (range g), if (obAt D e).1 = κ ∧ linkB g n D e p.1 p.2 = true then 1 else 0) ≤
      if (obAt D e).1 = κ then k - 1 + κ else 0 := by
    intro e he
    split_ifs with hi
    · simp only [hi, true_and]
      rw [← card_filter]
      have h3 := card_links_le (g := g) (n := n) (D := D) e
      have h4 := (Basic.clOf_wf hW (mem_range.1 he)).2.1
      omega
    · simp [hi]
  refine (sum_le_sum h2).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm]
end VariableBound.Net.Tests
