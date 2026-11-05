-- Prove2me | solution 1 for WidthK.Rule.add_heavy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:16:30.779678+00:00
-- url     : https://prove2.me/submissions/4e35460e-7307-4284-9cee-db62581c9e9c

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
import Theorems.Thm_WidthK_Step_card_over_le
import Theorems.Thm_WidthK_Step_card_of_mem_petals
import Theorems.Thm_Groundwork_PolyT_all
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
namespace WidthK
namespace Rule
theorem _root_.solution (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) :
    AddK (dg θ) F (petals F j H) (j - H.card) where
  ssub := by
    intro Q hQ
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
    obtain ⟨hCF, -, hHC⟩ := mem_filter.1 hC
    refine ⟨C, hCF, sdiff_subset, fun hsub => ?_⟩
    obtain ⟨x, hx⟩ := hB.heart.1
    exact (mem_sdiff.1 (hsub (hHC hx))).2 hx
  size := fun Q hQ => card_of_mem_petals hQ
  pos := Nat.sub_pos_of_lt hB.heart.2.1
  deg := by
    intro y
    have hH := card_pos.2 hB.heart.1
    have hlt := hB.heart.2.1
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hlt).ne'
    have h2 : ((petals F j H).filter fun D => y ∈ D).card ≤ θ s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · exact (card_filter_mem_le_one (fun Q hQ => (card_of_mem_petals hQ).trans hs) y).trans (hθ _)
      · by_cases hy : y ∈ H
        · rw [filter_eq_empty_iff.2]
          · exact Nat.zero_le _
          · intro Q hQ hyQ
            obtain ⟨C, -, rfl⟩ := mem_image.1 hQ
            exact (mem_sdiff.1 hyQ).2 hy
        · have hc : (insert y H).card = H.card + 1 := card_insert_of_notMem hy
          have hlt' : (Sparsify.over F j (insert y H)).card < θ s := by
            by_contra hcon
            refine hB.maxH (insert y H) (by omega) ⟨insert_nonempty y H, by omega, ?_⟩
            rw [hc, show j - (H.card + 1) = s by omega]
            exact not_lt.1 hcon
          refine le_trans (le_trans (card_le_card ?_) (card_image_le (f := fun C => C \ H))) hlt'.le
          intro Q hQ
          obtain ⟨hQ, hyQ⟩ := mem_filter.1 hQ
          obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
          obtain ⟨hCF, hcC, hHC⟩ := mem_filter.1 hC
          exact mem_image.2 ⟨C, mem_filter.2 ⟨hCF, hcC, insert_subset (mem_sdiff.1 hyQ).1 hHC⟩, rfl⟩
    rw [hs]
    have h1 := card_over_le hθ hB (s := s) (by omega) y
    simp only [dg, Nat.succ_eq_add_one]
    omega
end Rule
end WidthK
