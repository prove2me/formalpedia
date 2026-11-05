-- Prove2me | solution 1 for VariableBound.Net.Total.stTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:26:53.569556+00:00
-- url     : https://prove2.me/submissions/360a3500-5f0c-49cc-ae22-c4317e8d5977

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_VariableBound_Net_Total
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open VariableBound VariableBound.Net VariableBound.Net.Total
open Groundwork Groundwork.Prog Finset PaddedDescent.F
namespace VariableBound.Net.Total
theorem _root_.solution (hV : StVal) (hP : StProf) (hT : StTuples) : StTotal := by
  classical
  intro k g n nb M D fl hg hW
  have h1 : ∀ y ∈ Finset.range (nPr g D),
      (if admD k g n nb M D fl y = true then (netDN g (ctx g n D y fl)).value else 0) =
        ∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset,
          wt D fl P * (if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) := by
    intro y _
    rw [hV k g n D y fl hg hW]
    by_cases h : admD k g n nb M D fl y = true
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P _ => ?_
      by_cases hm : Match g n D y P
      · simp [h, hm]
      · simp [hm]
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← hT k n nb M D fl hW]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (objs D).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k g n nb M D fl P hg hW hsub
  rw [← Finset.mul_sum]
  by_cases hc : Lim nb M D fl P
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nPr g D), if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nPr g D), if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]
end VariableBound.Net.Total
