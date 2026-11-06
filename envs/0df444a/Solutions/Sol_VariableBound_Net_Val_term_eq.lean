-- Prove2me | solution 1 for VariableBound.Net.Val.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:55:38.495248+00:00
-- url     : https://prove2.me/submissions/d7b211fb-1975-4f9c-bc2a-47e26d92d511

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_VariableBound_Net_Val
import Theorems.Thm_VariableBound_Net_Val_WD_eq
import Theorems.Thm_VariableBound_Net_Val_netDN_W
import Theorems.Thm_P2M_VariableBound_Net_Val___eq_82bf20579481
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
namespace VariableBound.Net.Val
theorem _root_.solution (hL : StLab) (z : Fin g → List Bool) :
    (∏ a, (netDN g (ctx g n D y fl)).W a (z a)) *
        ∏ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
      by classical exact if Gd g n D z then
        (if ∀ a : Fin g, prof g n D y a (z a) = true then ∏ a : Fin g, wz g n D fl a (z a) else 0) else 0 := by
  classical
  simp only [netDN_W, WD_eq]
  by_cases hp : ∀ a : Fin g, (base g n D a (z a) && prof g n D y a (z a)) = true
  · have hb1 : ∀ a : Fin g, base g n D a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).1
    have hp1 : ∀ a : Fin g, prof g n D y a (z a) = true := fun a => (Bool.and_eq_true _ _ ▸ hp a).2
    have hΨ : ∀ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ i < (2 : ℕ), str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) then 1 else 0 :=
      fun p hpp => Ψ_eq hL (ne_of_lt (Finset.mem_filter.1 hpp).2) (hp1 p.1) (hp1 p.2)
    have hPs : ∏ p ∈ pairs (Fin g), (netDN g (ctx g n D y fl)).Ψ p.1 p.2 (z p.1) (z p.2) =
        if ∀ p ∈ pairs (Fin g), ∀ i < 2, str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) then 1 else 0 := by
      rw [Finset.prod_congr rfl hΨ, Finset.prod_ite_zero, Finset.prod_const_one]
      split_ifs <;> simp_all
    rw [hPs, Finset.prod_congr rfl fun a _ => if_pos (hp a), if_pos hp1]
    by_cases hG : Gd g n D z
    · have hall : ∀ p ∈ pairs (Fin g), ∀ i < 2, str g n D p.1 p.2 i (z p.1) = str g n D p.2 p.1 i (z p.2) :=
        fun p hpp => hG.2 p.1 p.2 (Finset.mem_filter.1 hpp).2
      rw [if_pos hG, if_pos hall, mul_one]
    · rw [if_neg hG, if_neg, mul_zero]
      intro h
      exact hG ⟨hb1, fun a a' haa => h (a, a') (Finset.mem_filter.2 ⟨Finset.mem_univ _, haa⟩)⟩
  · obtain ⟨a, ha⟩ := not_forall.1 hp
    rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha), zero_mul]
    by_cases hG : Gd g n D z
    · rw [if_pos hG, if_neg]
      intro h
      exact ha (by rw [hG.1 a, h a]; rfl)
    · rw [if_neg hG]
end VariableBound.Net.Val
