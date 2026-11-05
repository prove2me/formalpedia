-- Prove2me | solution 1 for UniformInK.Bound.bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:00.910172+00:00
-- url     : https://prove2.me/submissions/202bf2d6-91de-441e-a308-af273e5ccda3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_UniformInK_Bound_acc_le
import Theorems.Thm_UniformInK_Bound_subset_of
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
open UniformInK.Bound
variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}
namespace UniformInK.Bound
theorem _root_.solution (hT : ThrU k τ θ β) (hU : U.card ≤ 2 * n) (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n := by
  have hFU := subset_of hφ h
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  have ha := acc_le hT hU hFU hI ha0
  constructor
  · rw [sum_mul]
    exact hp.trans (sum_le_sum fun i hi => ha i (mem_range.1 hi))
  · refine ht.trans ?_
    rw [mul_sum]
    refine (sum_le_card_nsmul _ _ n fun r hr => ?_).trans (by simp)
    have har := ha r (mem_range.1 hr)
    have h1 : τ * hh r * β r ≤ n * β r := by
      calc τ * hh r * β r = hh r * (τ * β r) := by ring
        _ ≤ hh r * θ r := Nat.mul_le_mul_left _ (hT.mul r)
        _ ≤ a r := hh1 r
        _ ≤ β r * n := har
        _ = n * β r := Nat.mul_comm _ _
    rcases Nat.eq_zero_or_pos (β r) with h0 | h0
    · have h2 := (hh1 r).trans har
      rw [h0, Nat.zero_mul] at h2
      have h3 : hh r = 0 := by
        rcases Nat.eq_zero_or_pos (hh r) with h | h
        · exact h
        · exact absurd (Nat.mul_pos h (hT.pos r)) (by omega)
      rw [h3, Nat.mul_zero]; exact Nat.zero_le _
    · exact Nat.le_of_mul_le_mul_right h1 h0
end UniformInK.Bound
