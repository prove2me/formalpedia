-- Prove2me | solution 1 for SizeCircuit.stSizedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:11.486475+00:00
-- url     : https://prove2.me/submissions/5f38c233-7f0c-4958-9a6f-3c5796ada083

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_GraphProblems_Sized
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Sized
import Theorems.Thm_SizeCircuit_le_numVars
import Theorems.Thm_SizeCircuit_numVars_le
import Theorems.Thm_SizeCircuit_shaped_gamma
import Theorems.Thm_GraphProblems_cntN_dedup
import Theorems.Thm_GraphProblems_cntN_le
import Theorems.Thm_GraphProblems_ofWord_binary
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SizeCircuit_stGammaCount
attribute [local fun_prop] Groundwork.PolyT.dedup
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
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
namespace SizeCircuit
theorem _root_.solution : StSizedBy := by
  intro gates a hT w δ δE hδ hδE hle E c hE
  obtain ⟨c₁, hc₁⟩ := exists_nat_ge ((c : ℝ) * (2 : ℝ) ^ δ)
  obtain ⟨C', hC'⟩ : ∃ C', C' = c₁ + c * (a + 3) ^ c + c := ⟨_, rfl⟩
  have k1 : c₁ ≤ C' := by rw [hC', Nat.add_assoc]; exact Nat.le_add_right _ _
  have k2 : c * (a + 3) ^ c ≤ C' := by rw [hC']; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have k3 : c ≤ C' := by rw [hC']; exact Nat.le_add_left _ _
  refine ⟨C', fun n s ψ _ hψ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = numVars gates n s := ⟨_, rfl⟩
  have hNle : N ≤ (a + 1) * (n + 1) := hN ▸ numVars_le hT n s
  have hnN : n ≤ N := hN ▸ le_numVars gates n s
  have hshape : ∀ C ∈ (ψ ++ gamma gates n s).dedup, C.length ≤ max w 3 ∧ ∀ l ∈ C, l.1 < N := by
    intro C hC
    rcases List.mem_append.1 (List.mem_dedup.1 hC) with h | h
    · obtain ⟨h1, h2⟩ := hψ C h
      exact ⟨h1.trans (le_max_left _ _), fun l hl => lt_of_lt_of_le (h2 l hl) hnN⟩
    · obtain ⟨h1, h2⟩ := shaped_gamma hT n s C h
      exact ⟨h1.trans (le_max_right _ _), fun l hl => hN ▸ h2 l hl⟩
  obtain ⟨T, hr, hTb⟩ := hE N _ hshape (List.nodup_dedup _)
  have hin : withGamma gates (List.replicate n (), s, ψ) = (List.replicate N (), (ψ ++ gamma gates n s).dedup) := by
    rw [withGamma, hN]
    simp only [List.length_replicate]
  have hcount : cntN N (ψ ++ gamma gates n s) = cntS n s ψ := by
    rw [hN]
    exact stGammaCount gates a hT n s ψ fun C hC => (hψ C hC).2
  rw [← hin] at hr
  have h2 := Stepped.mapOut_runs (f := ofWord) (Stepped.mapIn_runs hr)
  rw [cntN_dedup, ofWord_binary (cntN_le _ _), hcount] at h2
  refine ⟨T, h2.mono le_rfl ?_, ?_⟩
  · obtain ⟨X, hX⟩ : ∃ X, X = n + ψ.length + 2 := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have h3 : N + 2 ≤ (a + 3) * X := by
      have e1 : (a + 1) * (n + 1) ≤ (a + 1) * X := Nat.mul_le_mul_left _ (by omega)
      have e2 : (a + 3) * X = (a + 1) * X + 2 * X := by ring
      omega
    calc c * (N + 2) ^ c ≤ c * ((a + 3) * X) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
      _ = c * (a + 3) ^ c * X ^ c := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ C' * X ^ C' := Nat.mul_le_mul k2 (Nat.pow_le_pow_right hX1 k3)
  · have hN' : (N : ℝ) ≤ ((a : ℝ) + 1) * ((n : ℝ) + 1) := by exact_mod_cast hNle
    have h1 : δE * N ≤ δ * n + δ := by
      calc δE * N ≤ δE * (((a : ℝ) + 1) * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hN' hδE
        _ = δE * ((a : ℝ) + 1) * ((n : ℝ) + 1) := by ring
        _ ≤ δ * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = δ * n + δ := by ring
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by positivity
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δE * N) := hTb
      _ ≤ c * (2 : ℝ) ^ (δ * n + δ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two h1) (Nat.cast_nonneg c)
      _ = c * (2 : ℝ) ^ δ * (2 : ℝ) ^ (δ * n) := by
        rw [Real.rpow_add two_pos]
        ring
      _ ≤ c₁ * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc₁ hp
      _ ≤ C' * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 k1) hp
end SizeCircuit
