-- Prove2me | solution 1 for Value.prod_across
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:31:59.836394+00:00
-- url     : https://prove2.me/submissions/d9b4a2f8-5c35-45d7-980f-5f496d6f758a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
attribute [local fun_prop] Groundwork.PolyT.filter
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
variable {g K : ℕ}
namespace Value
theorem _root_.solution (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, F p * F p.swap := by
  have h1 : ∏ γ, ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, F p = ∏ p : Fin g × Fin g with χ p.1 ≠ χ p.2, F p := by
    rw [← Finset.prod_fiberwise (univ.filter fun p : Fin g × Fin g => χ p.1 ≠ χ p.2) (fun p => χ p.1)]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ⟨fun h => ⟨fun e => h.2 (e ▸ h.1), h.1⟩, fun h => ⟨h.2, fun e => h.1 (h.2.trans e.symm)⟩⟩) fun _ _ => rfl
  have h2 : ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, F p.swap = ∏ p : Fin g × Fin g with p.2 < p.1 ∧ χ p.1 ≠ χ p.2, F p := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
    · intro p hp
      simp only [pairs, mem_filter, mem_univ, true_and] at hp
      exact mem_filter.2 ⟨mem_univ _, hp.1, hp.2.symm⟩
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp.1⟩, hp.2.symm⟩
  rw [h1, Finset.prod_mul_distrib, h2, pairs, Finset.filter_filter, ← Finset.prod_union]
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      rcases lt_trichotomy p.1 p.2 with h' | h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact absurd (congrArg χ h') h
      · exact Or.inr ⟨h', h⟩
    · rintro (h | h) <;> exact h.2
  · rw [Finset.disjoint_left]
    intro p hp hp'
    exact lt_asymm (mem_filter.1 hp).2.1 (mem_filter.1 hp').2.1
end Value
