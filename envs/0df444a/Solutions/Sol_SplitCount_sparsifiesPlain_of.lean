-- Prove2me | solution 1 for SplitCount.sparsifiesPlain_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:51.74699+00:00
-- url     : https://prove2.me/submissions/85470a4a-f1dd-47a9-9ec6-a11230fc9bd9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
import Theorems.Thm_SplitCount_leaves_map
import Theorems.Thm_SplitCount_round_iterate_map
import Theorems.Thm_SplitCount_stepC_withSide
import Theorems.Thm_SplitCount_length_leafF_le
import Theorems.Thm_SplitCount_mem_leafF_withSide
import Theorems.Thm_SplitCount_cntN_withSide
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
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
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width
namespace SplitCount
theorem _root_.solution {k : ℕ} {ε : ℝ} {θ : ℕ → ℕ} {Dd Bl Sk : ℕ} (h : SparsifiesC k ε (stepC θ k) Dd Bl Sk) : SparsifiesPlain k ε (stepC θ k) Dd Bl Sk := by
  intro n ψ hψ
  obtain ⟨t1, t2, t3, t4⟩ := h n ψ hψ
  obtain ⟨u, hu⟩ : ∃ u : List Unit, u = List.replicate n () := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : CNode, r₀ = (rootP ψ, []) := ⟨_, rfl⟩
  have hC : rootC (List.replicate n (), ψ) = withSide (taut n) r₀ := by simp [rootC, withSide, hr₀]
  have hP : rootPlain (List.replicate n (), ψ) = (u, r₀) := by rw [hu, hr₀]; rfl
  have cC := stepC_withSide θ k (taut n)
  have cP : ∀ y : CNode, stepPlain (stepC θ k) (u, y) = (stepC θ k y).map fun lh => ((u, lh.1), (u, lh.2)) := fun _ => rfl
  rw [hC] at t1 t2 t3 t4
  rw [leaves_map cC] at t1 t2 t3
  rw [hP, leaves_map (f := Prod.mk u) cP]
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC θ k) (Dd * n) r₀ := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3 ⊢
  refine ⟨by simpa using t1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a1, a2, a3, -⟩ := t2 _ (List.mem_map_of_mem hy)
    refine ⟨?_, hu, (length_leafF_le _ y).trans a2, fun C hC => a3 C (mem_leafF_withSide hC)⟩
    rw [cC, Option.map_eq_none_iff] at a1
    rw [cP, a1]
    rfl
  · rw [t3, List.map_map, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun y _ => cntN_withSide n n y)
  · intro i
    have eC := round_iterate_map cC i ([r₀], [])
    have eP := round_iterate_map (f := Prod.mk u) cP i ([r₀], [])
    obtain ⟨b1, b2⟩ := t4 i
    simp only [List.map_cons, List.map_nil] at eC eP
    rw [eC] at b1 b2
    rw [eP]
    refine ⟨by simpa using b1, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a2, a3⟩ := b2 _ (List.mem_map_of_mem hy)
    exact ⟨hu, (length_leafF_le _ y).trans a2, fun C hC => a3 C (mem_leafF_withSide hC)⟩
end SplitCount
