-- Prove2me | solution 1 for Sat3Graph.stDominating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:40.959853+00:00
-- url     : https://prove2.me/submissions/39ffcd70-5c74-4b65-b6a2-3e35be1b30f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Dominating
import Theorems.Thm_Sat3Graph_sum_ne_zero_iff
import Theorems.Thm_Sat3Graph_size_dnode_le
import Theorems.Thm_GraphProblems_stDecide
import Theorems.Thm_GraphProblems_stDom
import Theorems.Thm_GraphProblems_stRead2
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_walk_runs
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
import Theorems.Thm_Sat3Graph_stAskSized
import Theorems.Thm_SplitSat_size_list_le
attribute [local fun_prop] Groundwork.PolyT.any
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
open Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat
namespace Sat3Graph
theorem _root_.solution : StDominating := by
  intro gates a hT w δ δ₃ hδ h0 hsh hle D c hD
  obtain ⟨c₁, hA⟩ := stAskSized gates a hT w (3 * (w - 3)) (δ / 2) δ₃ (by positivity) h0 (by push_cast; exact hle) D c hD
  refine ⟨8 * w + c₁ + 34, fun n G s hs => ?_⟩
  obtain ⟨t1, t2, t3, t4⟩ := hsh n s (matrix G)
  obtain ⟨x0, hx0⟩ : ∃ x0 : List Unit × ℕ × List Bool, x0 = (List.replicate n (), s, matrix G) := ⟨_, rfl⟩
  rw [← hx0] at t1 t2 t3 t4
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepD w) (2 * n) (rootD x0) := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3
  have hleaf : ∀ x ∈ leaves (stepD w) (2 * n) (rootD x0), (Stepped.mapIn leafD (askSized gates D)).Runs x ⌊(c₁ : ℝ) * E⌋₊ (c₁ * X ^ c₁)
      (decide (cntS n s (leafD x).2.2 ≠ 0)) := by
    intro x hx
    rw [← hL] at hx
    obtain ⟨-, h1, h2, h3⟩ := t2 x hx
    have hB : (w - 3) * (leafD x).2.2.length ≤ 3 * (w - 3) * (n + 1) := by
      generalize w - 3 = u
      calc u * (leafD x).2.2.length ≤ u * (3 * n) := Nat.mul_le_mul_left _ h3
        _ ≤ 3 * u * (n + 1) := by nlinarith [Nat.zero_le u]
    obtain ⟨T, b, hr, hb, hTle⟩ := hA n s (leafD x).2.2 hs h2 hB
    have e : leafD x = (List.replicate n (), s, (leafD x).2.2) := by simp [leafD, h1]
    have eb : decide (cntS n s (leafD x).2.2 ≠ 0) = b := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact hb.symm
    rw [eb]
    rw [← e] at hr
    exact (Stepped.mapIn_runs hr).mono (Nat.le_floor (hE ▸ hTle)) (le_of_eq (by rw [hX]))
  have hstack : ∀ i, size ((round (stepD w))^[i] ([rootD x0], [])).1 ≤ (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 := by
    intro i
    obtain ⟨s1, s2⟩ := t4 i
    exact SplitSat.size_list_le s1 fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := s2 x hx
      exact hX ▸ size_dnode_le hs h1 h2 h3 h4 h5
  have wr := Stepped.walk_runs (stepD w) (root := rootD) (T := Stepped.mapIn leafD (askSized gates D)) (2 * n) x0
    (fun x hx => (t2 x (hL ▸ hx)).1) (fun x => decide (cntS n s (leafD x).2.2 ≠ 0)) ⌊(c₁ : ℝ) * E⌋₊ (c₁ * X ^ c₁) _ hleaf hstack
  rw [← hL] at wr
  have hread : read2 (codeWith G s) = x0 := by rw [stRead2 n G s, hx0]
  have wr' : (Stepped.walk (stepD w) rootD (Stepped.mapIn leafD (askSized gates D))).Runs (read2 (codeWith G s)) (L.length * (⌊(c₁ : ℝ) * E⌋₊ + 2))
      ((2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (1 + (c₁ * X ^ c₁ + 1)) + 1) (L.any fun x => decide (cntS n s (leafD x).2.2 ≠ 0)) := by
    rw [hread]
    exact wr
  refine ⟨_, _, (Stepped.mapIn_runs wr').mono le_rfl ?_, ?_, ?_⟩
  · -- sizes
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    obtain ⟨P, hP⟩ : ∃ P, P = X ^ (c₁ + 4) := ⟨_, rfl⟩
    have hP0 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ hX1
    have hP4 : X ^ 4 ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
    have hPc : X ^ c₁ ≤ P := by rw [hP]; exact Nat.pow_le_pow_right hX1 (by omega)
    have a1 : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (8 * w + 26) * P := by
      have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
      calc (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) ≤ (2 * X) * ((4 * w + 13) * X ^ 3) := by
            refine Nat.mul_le_mul (by omega) ?_
            have : (4 * w + 13) * X ^ 3 = (4 * w + 12) * X ^ 3 + X ^ 3 := by ring
            omega
        _ = (8 * w + 26) * X ^ 4 := by ring
        _ ≤ (8 * w + 26) * P := Nat.mul_le_mul_left _ hP4
    have a2 : c₁ * X ^ c₁ ≤ c₁ * P := Nat.mul_le_mul_left _ hPc
    have total : (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (1 + (c₁ * X ^ c₁ + 1)) + 1 ≤ (8 * w + c₁ + 34) * P := by
      have eK : (8 * w + c₁ + 34) * P = (8 * w + 26) * P + c₁ * P + 8 * P := by ring
      omega
    refine total.trans ?_
    rw [hP]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  · -- the answer
    rw [List.any_eq_true]
    simp only [decide_eq_true_eq]
    rw [← sum_ne_zero_iff (fun x => cntS n s (leafD x).2.2) L, ← t3, stDom n G s]
    exact (stDecide n G s hs).2.2.2.symm
  · -- steps
    have hfl : ((⌊(c₁ : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c₁ : ℝ) * E := Nat.floor_le (by positivity)
    have hLE : (L.length : ℝ) ≤ E := hE ▸ t1
    have hEE : E * E = (2 : ℝ) ^ (δ * n) := by
      rw [hE, ← Real.rpow_add two_pos]
      congr 1
      ring
    have hE0 : 0 ≤ E := by linarith
    push_cast
    calc (L.length : ℝ) * (((⌊(c₁ : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
        ≤ E * ((c₁ : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE0
      _ = ((c₁ : ℝ) + 2) * (E * E) := by ring
      _ = ((c₁ : ℝ) + 2) * (2 : ℝ) ^ (δ * n) := by rw [hEE]
      _ ≤ (8 * (w : ℝ) + c₁ + 34) * (2 : ℝ) ^ (δ * n) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
        linarith
end Sat3Graph
