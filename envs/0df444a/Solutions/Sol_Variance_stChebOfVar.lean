-- Prove2me | solution 1 for Variance.stChebOfVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:52:43.789388+00:00
-- url     : https://prove2.me/submissions/93948bef-17fa-4d84-a770-745e8fe26f15

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
import Theorems.Thm_Variance_Y_le_total
import Theorems.Thm_Groundwork_Colouring_cheb
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


section
namespace Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
private theorem eth16a5ce4_cheb_count {Ω : Type} [Fintype Ω] (X : Ω → ℕ) (A m V t s : ℕ) (hV : ∑ χ, ((A : ℤ) * X χ - m) ^ 2 ≤ V) :
    #{χ : Ω | t * m + s < t * (A * X χ)} * s ^ 2 ≤ t ^ 2 * V := by
  have hc := Groundwork.Colouring.cheb (fun χ : Ω => (t : ℤ) * ((A : ℤ) * X χ - m)) s (by positivity)
  have hsub : #{χ : Ω | t * m + s < t * (A * X χ)} ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    zify at h
    linarith
  have hsum : ∑ χ : Ω, ((t : ℤ) * ((A : ℤ) * X χ - m)) ^ 2 = (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 := by
    simp only [mul_pow, mul_sum]
  rw [hsum] at hc
  have a1 : (#{χ : Ω | t * m + s < t * (A * X χ)} : ℤ) * (s : ℤ) ^ 2 ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} : ℤ) * (s : ℤ) ^ 2 :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hsub) (sq_nonneg _)
  have a2 : (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 ≤ (t : ℤ) ^ 2 * V := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
  have a3 := a1.trans (hc.trans a2)
  exact_mod_cast a3
end Variance
set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution : StChebOfVar := by
  intro g K P c γ γ' hne hV hU
  unfold VarBound at hV
  unfold ChebBound
  have hY : ∀ χ : Fin g → Fin K, Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := fun χ => Y_le_total c χ hne
  generalize (∑ a, ∑ b ∈ univ.erase a, c a b) = U at hV hU hY ⊢
  rcases Nat.eq_zero_or_pos (g * P) with h0 | hpos
  · have hU0 : U = 0 := by omega
    have : ({χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'} : Finset (Fin g → Fin K)) = ∅ := by
      refine filter_false_of_mem fun χ _ => ?_
      have hY0 : Y c χ γ γ' = 0 := by have := hY χ; omega
      simp [hY0]
    rw [this]; simp
  have hc := eth16a5ce4_cheb_count (fun χ : Fin g → Fin K => Y c χ γ γ') (K ^ 2) U _ K (g * P) hV
  have e : ∀ χ : Fin g → Fin K, K * (K ^ 2 * Y c χ γ γ') = K ^ 3 * Y c χ γ γ' := fun χ => by ring
  simp only [e] at hc
  have hPpos : 0 < P := Nat.pos_of_mul_pos_left hpos
  have : (g * #{χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'}) * (g * P * P) ≤ (4 * K ^ 6 * K ^ g) * (g * P * P) := by
    calc _ = #{χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'} * (g * P) ^ 2 := by ring
      _ ≤ K ^ 2 * (4 * P * U * K ^ 4 * K ^ g) := hc
      _ = (4 * K ^ 6 * K ^ g * P) * U := by ring
      _ ≤ (4 * K ^ 6 * K ^ g * P) * (g * P) := Nat.mul_le_mul_left _ hU
      _ = (4 * K ^ 6 * K ^ g) * (g * P * P) := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hpos hPpos)
end Variance
