-- Prove2me | solution 1 for Value.stCliqueValueOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:46:56.485391+00:00
-- url     : https://prove2.me/submissions/340acba3-ab1b-41b4-b84f-1120fd9835c3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique
import Theorems.Thm_Eight_SecNetworks_star_mem
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_Stepped_Runs_unique
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
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_pr_of_lt
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
import Theorems.Thm_Value_star_swap
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
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
namespace Value
theorem _root_.solution : StCliqueValueOf := by
  intro h1 h2 h3 K lam W
  classical
  obtain ⟨hA, hB⟩ := h3 K lam
  rw [h1 K lam (tablesOn lam W), ← Finset.sum_filter_of_ne (p := CopiesAgree lam) fun z _ hne => by_contra fun hn => hne ((h2 K lam (tablesOn lam W) z).1 hn)]
  symm
  have hag : ∀ (Λ : Fin K × Fin K → List Bool) (z : Fin K → List Bool), (∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w') → CopiesAgree lam z := by
    intro Λ z hz p hp
    have hlt : p.1 < p.2 := (mem_filter.1 hp).2
    rw [hz p.1 p.2 hlt.ne', hz p.2 p.1 hlt.ne, star_swap]
  refine Finset.sum_bij (fun Λ hΛ => (hA Λ hΛ).exists.choose) ?_ ?_ ?_ ?_
  · intro Λ hΛ
    have hs := (hA Λ hΛ).exists.choose_spec
    exact mem_filter.2 ⟨hs.1, hag Λ _ hs.2⟩
  · intro Λ₁ h₁ Λ₂ h₂ e
    have hs₁ := (hA Λ₁ h₁).exists.choose_spec
    have hs₂ := (hA Λ₂ h₂).exists.choose_spec
    rw [e] at hs₁
    funext p
    by_cases hp : p.1 < p.2
    · have e₁ := (hs₁.2 p.1 p.2 hp.ne').symm.trans (hs₂.2 p.1 p.2 hp.ne')
      change Λ₁ (pr p.1 p.2) = Λ₂ (pr p.1 p.2) at e₁
      rw [(pr_of_lt hp).1] at e₁
      exact e₁
    · rw [((mem_tuples _ _ _ _).1 h₁ p).2 hp, ((mem_tuples _ _ _ _).1 h₂ p).2 hp]
  · intro z hz
    obtain ⟨hz1, hz2⟩ := mem_filter.1 hz
    obtain ⟨Λ, hΛ, hrel⟩ := hB z hz1 hz2
    exact ⟨Λ, hΛ, (hA Λ hΛ).unique (hA Λ hΛ).exists.choose_spec ⟨hz1, hrel⟩⟩
  · intro Λ hΛ
    have hs := (hA Λ hΛ).exists.choose_spec
    rw [(h2 K lam (tablesOn lam W) _).2 (hag Λ _ hs.2)]
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold tablesOn
    congr 1
    funext w'
    by_cases hw : w' = w
    · rw [if_pos hw, hw]
      exact ((mem_tuples _ _ _ _).1 (star_mem hΛ w) w).2 (by simp)
    · rw [if_neg hw, hs.2 w w' hw]
end Value
