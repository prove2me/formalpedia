-- Prove2me | solution 1 for PaddedDescent.F.Mark.Sum.stMarkSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:00.45509+00:00
-- url     : https://prove2.me/submissions/fe98a041-009a-47f6-9a49-37acda1ce28a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_PaddedDescent_F_MarkSum
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Sum
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace PaddedDescent.F.Mark.Sum
theorem _root_.solution (hV : StMarkVal) (hP : StProfSum) (hS : StPiSum) : StMarkSum := by
  classical
  intro k gu nu βu bu w Ls hg h0 hb hw
  have h1 : ∀ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
      (if adm k gu.length nu.length w Ls y = true then (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value else 0) =
        ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
          sgnP Ls P * (if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) := by
    intro y _
    rw [hV k gu nu βu bu Ls y hg h0 hb hw]
    by_cases h : adm k gu.length nu.length w Ls y = true
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P _ => ?_
      by_cases hm : Match gu.length nu.length Ls y P
      · simp [h, hm]
      · simp [hm]
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  unfold trunc
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm, ← hS w Ls (Mark.ext σ)]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k gu.length nu.length w Ls P hg hw hsub
  rw [← Finset.mul_sum]
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]
end PaddedDescent.F.Mark.Sum
