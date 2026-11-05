-- Prove2me | solution 1 for PaddedDescent.F.Mark.Pi.sum_capped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:04.344192+00:00
-- url     : https://prove2.me/submissions/85ff83ed-12fc-41d5-843d-3b6b09909aa2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_layers
import Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_cap
import Theorems.Thm_PaddedDescent_F_Mark_Pi_prod_sign
import Theorems.Thm_Groundwork_PolyT_filter
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
namespace PaddedDescent.F.Mark.Pi
theorem _root_.solution (lay : ι → ℕ) (R w : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset.filter (fun X => ∀ i < R, (X.filter fun e => lay e = i).card ≤ w),
        (-1 : ℤ) ^ (X.filter fun e => 1 ≤ lay e).card =
      ∏ i ∈ range R, ∑ j ∈ range (w + 1),
        (if i = 0 then (1 : ℤ) else -1) ^ j * ((V.filter fun e => lay e = i).card.choose j : ℤ) := by
  rw [← prod_congr rfl fun i _ => sum_powerset_cap (V.filter fun e => lay e = i) w (if i = 0 then (1 : ℤ) else -1),
    ← sum_powerset_layers lay (fun i P => if P.card ≤ w then (if i = 0 then (1 : ℤ) else -1) ^ P.card else 0) R V hV,
    sum_filter]
  refine sum_congr rfl fun X hX => ?_
  have hXV := mem_powerset.1 hX
  split_ifs with h
  · rw [← prod_sign lay R X fun e he => hV e (hXV he)]
    exact prod_congr rfl fun i hi => (if_pos (h i (mem_range.1 hi))).symm
  · simp only [not_forall] at h
    obtain ⟨i, hi, hw⟩ := h
    exact (prod_eq_zero (mem_range.2 hi) (if_neg hw)).symm
end PaddedDescent.F.Mark.Pi
