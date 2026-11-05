-- Prove2me | solution 1 for Variance.stSomePairOfCheb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:53.675768+00:00
-- url     : https://prove2.me/submissions/79fbdeed-34c7-4b7a-980c-b10267669663

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Var
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_SecNetworks_Grouping
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Grouping
import Theorems.Thm_Eight_SecNetworks_Y_symm
import Theorems.Thm_Eight_SecNetworks_card_pairs_lt
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution : StSomePairOfCheb := by
  intro g K P c hK hs hC
  have hsub : ({χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} : Finset (Fin g → Fin K)) ⊆
      ({p : Fin K × Fin K | p.1 < p.2} : Finset (Fin K × Fin K)).biUnion fun p => {χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} := by
    intro χ h
    simp only [mem_filter, mem_univ, true_and] at h
    obtain ⟨γ, γ', hne, hb⟩ := h
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Prod.exists]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨γ, γ', hlt, hb⟩
    · exact ⟨γ', γ, hgt, by rwa [Y_symm hs]⟩
  have hN : 0 < K ^ g := pow_pos hK g
  have h6 : 0 < K ^ 6 := pow_pos hK 6
  have hlt := card_pairs_lt hK
  have h1 : g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'}
      ≤ #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) := by
    calc _ ≤ g * ∑ p : Fin K × Fin K with p.1 < p.2, #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} :=
          Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
      _ = ∑ p : Fin K × Fin K with p.1 < p.2, g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} := mul_sum _ _ _
      _ ≤ ∑ _p : Fin K × Fin K with _p.1 < _p.2, 4 * K ^ 6 * K ^ g := sum_le_sum fun p hp => hC p.1 p.2 (mem_filter.1 hp).2.ne
      _ = _ := by simp
  have h2 : #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) < 2 * K ^ 8 * K ^ g := by
    calc #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) = (2 * #{p : Fin K × Fin K | p.1 < p.2}) * (2 * K ^ 6 * K ^ g) := by ring
      _ < K ^ 2 * (2 * K ^ 6 * K ^ g) := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 2 * K ^ 8 * K ^ g := by ring
  exact lt_of_le_of_lt h1 h2
end Variance
