-- Prove2me | solution 1 for SparsificationLemma.Shrink.length_step_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:35.060121+00:00
-- url     : https://prove2.me/submissions/2682e3a8-cd16-4eca-9d6b-aceaf5d1a9bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_Shrink
import Theorems.Thm_SparsificationLemma_Shrink_card_light_le
import Theorems.Thm_SparsificationLemma_Shrink_card_heavy_le
import Theorems.Thm_CountKSat_ProgC_stepC_some
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_WidthK_Node_heavy
import Theorems.Thm_WidthK_Node_light
import Theorems.Thm_WidthK_ProgMain_NF_singleton
import Theorems.Thm_WidthK_ProgMain_nf_addP
import Theorems.Thm_WidthK_ProgMain_nf_length_eq
import Theorems.Thm_WidthK_ProgMain_toFin_addP
import Theorems.Thm_WidthK_ProgMain_toFin_singleton
import Theorems.Thm_WidthK_Refine_stRefines
import Theorems.Thm_WidthK_stHeavyEq
import Theorems.Thm_WidthK_stLightEq
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
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain CountKSat
open SparsificationLemma.Shrink
variable {α : Type} [DecidableEq α] {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}
namespace SparsificationLemma.Shrink
theorem _root_.solution {k : ℕ} (hθ : ∀ i, 1 ≤ θ i) {x l h : CNode} (hx : NF x.1) (hred : Reduced (toFin x.1)) (hst : stepC θ k x = some (l, h)) :
    l.1.length ≤ x.1.length ∧ h.1.length ≤ x.1.length := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := ProgC.stepC_some hst
  obtain ⟨j, hrule, hP, hnfP, hH⟩ := (Refine.stRefines θ k hθ).some x.1 H P hx hp
  have e1 : toFin (addP [H] x.1) = light (toFin x.1) H.toFinset := by
    rw [toFin_addP, toFin_singleton, stLightEq _ θ _ j _ hθ hred hrule.heart]
    simp
  have e2 : toFin (addP P x.1) = heavy (toFin x.1) j H.toFinset := by
    rw [toFin_addP, hP, stHeavyEq _ θ _ j _ hred hrule.heart]
  constructor
  · show (addP [H] x.1).length ≤ x.1.length
    rw [nf_length_eq (nf_addP (NF_singleton hH) hx), nf_length_eq hx, e1]
    exact card_light_le hθ hred hrule.heart
  · show (addP P x.1).length ≤ x.1.length
    rw [nf_length_eq (nf_addP hnfP hx), nf_length_eq hx, e2]
    exact card_heavy_le hred hrule.heart
end SparsificationLemma.Shrink
