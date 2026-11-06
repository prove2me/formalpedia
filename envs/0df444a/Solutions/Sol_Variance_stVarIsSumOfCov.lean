-- Prove2me | solution 1 for Variance.stVarIsSumOfCov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:53.262378+00:00
-- url     : https://prove2.me/submissions/af862d7a-f1f4-4d8a-abf3-0fa376ba2728

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
import Theorems.Thm_Variance_stMean
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
import Theorems.Thm_Variance_stYIsSum
import Theorems.Thm_Variance_sum_ordered_c
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
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StVarIsSumOfCov := by
  intro g K c γ γ' hne
  have hM := stMean g K c γ γ' hne
  rw [← sum_ordered_c] at hM ⊢
  have hy : ∀ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) = ∑ p ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * (if Contributes γ γ' χ p then 1 else 0) := by
    intro χ
    rw [stYIsSum g K c χ γ γ' hne]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have hsq : ∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) ^ 2
      = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ) := by
    simp only [hy, sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    rw [card_filter]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun χ _ => ?_
    by_cases h1 : Contributes γ γ' χ p
    · by_cases h2 : Contributes γ γ' χ q
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
        ring
      · rw [if_neg h2, if_neg (show ¬ (Contributes γ γ' χ p ∧ Contributes γ γ' χ q) from fun h => h2 h.2)]
        ring
    · rw [if_neg h1, if_neg (show ¬ (Contributes γ γ' χ p ∧ Contributes γ γ' χ q) from fun h => h1 h.1)]
      ring
  have hUU : (((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ)) ^ 2 = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) := by
    push_cast
    rw [sq, sum_mul_sum]
  have hM' : (∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ)) * (K : ℤ) ^ 2 = (K : ℤ) ^ g * ((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ) := by exact_mod_cast hM
  have hcard : (∑ _χ : Fin g → Fin K, (1 : ℤ)) = (K : ℤ) ^ g := by simp
  generalize ((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ) = U at hUU hM' ⊢
  have hL : ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * ((Y c χ γ γ' : ℕ) : ℤ) - U) ^ 2
      = (K : ℤ) ^ 4 * ∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) ^ 2 - 2 * U * ((∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ)) * (K : ℤ) ^ 2) + U ^ 2 * ∑ _χ : Fin g → Fin K, (1 : ℤ) := by
    rw [mul_sum, sum_mul, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun χ _ => ?_
    push_cast
    ring
  have hR : ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * cov γ γ' p q
      = (K : ℤ) ^ 4 * (∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ))
        - (K : ℤ) ^ g * ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    unfold cov
    ring
  rw [hL, hR, hM', hcard, hsq, ← hUU]
  ring
end Variance
