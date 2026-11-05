-- Prove2me | solution 1 for WidthK.Leaf.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:17:36.285491+00:00
-- url     : https://prove2.me/submissions/f50e9f2e-1081-4afe-9a1a-2a315879610c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_WidthK_Step_card_filter_mem_le_one
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Sparsify_mul_card_le
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
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open Step
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
variable {n : ℕ} {U : Finset α} {β : ℕ → ℕ}
namespace WidthK
namespace Leaf
theorem _root_.solution (hθ : ∀ i, 0 < θ i) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : Leaf θ k F)
    (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) : F.card ≤ 2 * n * ∑ i ∈ range k, θ i := by
  have hlay : ∀ i < k, (lay F (i + 1)).card ≤ 2 * n * θ i := by
    intro i hi
    have hd : ∀ y, ((lay F (i + 1)).filter fun C => y ∈ C).card ≤ θ i := by
      intro y
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact (card_filter_mem_le_one (fun C hC => (mem_filter.1 hC).2) y).trans (hθ 0)
      · by_contra hc
        refine h (i + 1) hi {y} ⟨singleton_nonempty y, by rw [card_singleton]; omega, ?_⟩
        rw [card_singleton, Nat.add_sub_cancel]
        simpa only [lay, Sparsify.over, filter_filter, singleton_subset_iff] using (not_le.1 hc).le
    have := mul_card_le U (lay F (i + 1)) (i + 1) (θ i) (fun C hC => hFU C (mem_filter.1 hC).1)
      (fun C hC => (mem_filter.1 hC).2) hd
    calc (lay F (i + 1)).card ≤ (i + 1) * (lay F (i + 1)).card := Nat.le_mul_of_pos_left _ (Nat.succ_pos i)
      _ ≤ U.card * θ i := this
      _ ≤ 2 * n * θ i := Nat.mul_le_mul_right _ hU
  have hsub : F ⊆ (range k).biUnion fun i => lay F (i + 1) := by
    intro C hC
    obtain ⟨h1, h2⟩ := hF C hC
    exact mem_biUnion.2 ⟨C.card - 1, mem_range.2 (by omega), mem_filter.2 ⟨hC, by omega⟩⟩
  calc F.card ≤ ((range k).biUnion fun i => lay F (i + 1)).card := card_le_card hsub
    _ ≤ ∑ i ∈ range k, (lay F (i + 1)).card := card_biUnion_le
    _ ≤ ∑ i ∈ range k, 2 * n * θ i := sum_le_sum fun i hi => hlay i (mem_range.1 hi)
    _ = 2 * n * ∑ i ∈ range k, θ i := by rw [mul_sum]
end Leaf
end WidthK
