-- Prove2me | solution 1 for UniformInK.stTreeU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:10.655567+00:00
-- url     : https://prove2.me/submissions/0b2da4f6-faa8-4bd1-bbbf-ff33a3a645f7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Tree_Tree
import Theorems.Thm_UniformInK_Tree_one_le_thetaU
import Theorems.Thm_CountKSatRate_Tree_tree_of
import Theorems.Thm_CountKSat_stRootCount
import Theorems.Thm_CountKSat_stStepCount
import Theorems.Thm_CountKSat_stSumLeaves
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
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_occ_le_of_none
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_Refine_stRefines
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



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate WidthK.Prog
namespace UniformInK
theorem _root_.solution (hIf : StIfaceU) : StTreeU := by
  intro k τ n hk hτk hτ8 ψ hψ
  have hτ : 1 ≤ τ := (Nat.one_le_pow 2 k hk).trans hτk
  have hθ : ∀ i, 1 ≤ thetaU τ i := Tree.one_le_thetaU hτ
  have hI := hIf τ k n hk hτ8
  have hOk : WidthK.ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := WidthK.ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [WidthK.ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hT : k * n < (k * n / τ + 1) * τ := by
    calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  have hB : n * τ + k * (k * n) ≤ 2 * n * τ := by
    have := Nat.mul_le_mul_left n hτk
    calc n * τ + k * (k * n) = n * τ + n * k ^ 2 := by ring
      _ ≤ n * τ + n * τ := by omega
      _ = 2 * n * τ := by ring
  obtain ⟨c1, c2, c3, c4⟩ := CountKSatRate.Tree.tree_of stStepCount stRootCount stSumLeaves hθ hI (WidthK.Refine.stRefines _ k hθ) hT hB ψ hOk
    fun C hC => (hψ C hC).2
  have er : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [er]
  refine ⟨c1, fun x hx => ?_, c3, c4⟩
  obtain ⟨d1, d2, d3, p', t', hx'⟩ := c2 x hx
  have hne : ∀ C ∈ x.1, C ≠ [] := by
    intro C hC
    obtain ⟨C', hC', hsub, hne⟩ := hx'.1.2.2.1 _ (WidthK.ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
    obtain ⟨-, b, -⟩ := hx'.1.2.1 C' hC'
    exact (List.toFinset_nonempty_iff C).1 (hne b)
  have hst : stepK (thetaU τ) k x.1 = none := by simpa [stepC, stepK] using d1
  exact ⟨d1, d2.trans (le_of_eq (by ring)), fun C hC => ⟨hne C hC, d3 C hC⟩,
    fun v => PaddedDescent.F.Mark.Deg.length_occ_le_of_none hθ hx'.1.1 (fun C hC => ⟨hne C hC, (d3 C hC).1⟩) hst v,
    fun C hC => ⟨hx'.2.2.2.2 C hC, (hx'.2.2.1 C hC).2⟩⟩
end UniformInK
