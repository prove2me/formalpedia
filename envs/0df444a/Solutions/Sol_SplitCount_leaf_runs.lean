-- Prove2me | solution 1 for SplitCount.leaf_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:35.939395+00:00
-- url     : https://prove2.me/submissions/ea24abe0-27d9-45e6-b050-26b8a316ca03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
import Theorems.Thm_SplitCount_leaf_size
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_stStepThree
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
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution {k Bl A : ℕ} {D : StepMachine (List Unit × Fml) ℕ} {δ δ' : ℝ} (hδ' : 0 ≤ δ')
    (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) {n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) {x : NNode}
    (hx1 : x.1 = List.replicate n ()) (hxl : (leafF x.2).length ≤ Bl * n) (hxc : ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    (Stepped.mapIn leafPlain (Stepped.mapIn widthP D)).Runs x ⌊(A : ℝ) * (2 : ℝ) ^ (δ / 3 * n)⌋₊ (A * (leafConst k Bl * M ^ 2) ^ A) (cntN n (leafF x.2)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = leafF x.2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = max k 3 := ⟨_, rfl⟩
  rw [← hΨ] at hxl hxc ⊢
  have hw3 : 3 ≤ w := hw ▸ le_max_right _ _
  have hkw : max k 2 ≤ w := by rw [hw]; omega
  -- the width reduction («Second, …» in the proof of Corollary 6)
  obtain ⟨g1, g2, -, g4, g5, g6⟩ := stStepThree w n Ψ (fun C hC => (hxc C hC).1.trans hkw) fun C hC => (hxc C hC).2
  obtain ⟨p, hp⟩ : ∃ p, p = widthP (List.replicate n (), Ψ) := ⟨_, rfl⟩
  rw [← hp] at g1 g2 g4 g5 g6
  have hp2 : (List.replicate p.1.length (), p.2) = p := by rw [hp]; simp [widthP]
  -- counting for the 3-CNF (the first sentence of the proof of Corollary 6)
  obtain ⟨T, r, hT⟩ := hD p.1.length p.2 g1 g2
  rw [hp2, g6] at r
  have hx : widthP (leafPlain x) = p := by rw [hp, leafPlain, hx1, hΨ]
  refine (Stepped.mapIn_runs (Stepped.mapIn_runs (by rw [hx]; exact r))).mono (Nat.le_floor (hT.trans ?_)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ A))
  · -- «with a small enough value in place of δ»
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (Nat.cast_nonneg A)
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((w - 3 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := hq ▸ Nat.cast_nonneg _
    have c1 : ((max k 3 : ℕ) : ℝ) - 3 = q := by rw [hq, ← hw, Nat.cast_sub hw3]; norm_num
    rw [c1] at hδB
    have c2 : (p.2.length : ℝ) ≤ (Ψ.length : ℝ) + 3 * (q * (Ψ.length : ℝ)) := by rw [hq]; exact_mod_cast g5
    have c3 : (Ψ.length : ℝ) ≤ (Bl : ℝ) * n := by exact_mod_cast hxl
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have c4 : (Ψ.length : ℝ) ≤ ((Bl : ℝ) + 1) * n := by linarith
    have c5 : (1 + 3 * q) * (Ψ.length : ℝ) ≤ (1 + 3 * q) * (((Bl : ℝ) + 1) * n) := mul_le_mul_of_nonneg_left c4 (by positivity)
    calc δ' * (p.2.length : ℝ) ≤ δ' * ((1 + 3 * q) * (((Bl : ℝ) + 1) * n)) := mul_le_mul_of_nonneg_left (by linarith) hδ'
      _ = δ' * ((1 + 3 * q) * ((Bl : ℝ) + 1)) * n := by ring
      _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB hn0
  · rw [leafConst, ← hw]
    exact leaf_size hn h1 hxl g1 g2 g4 g5
end SplitCount
