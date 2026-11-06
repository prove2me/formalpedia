-- Prove2me | solution 1 for SparsificationLemma.stGen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:22.724541+00:00
-- url     : https://prove2.me/submissions/ceb3d5b6-47a3-42c8-b9d1-9b319da52a9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Gen
import Theorems.Thm_SparsificationLemma_Gen_withSideClauses
import Theorems.Thm_SparsificationLemma_Gen_occN_out_le
import Theorems.Thm_CountKSatRate_Leaf_length_occ_sideU_le
import Theorems.Thm_CountKSatRate_Leaf_mem_sideU
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
namespace SparsificationLemma
theorem _root_.solution (hSide : StSide) : StGen := by
  intro k τ n D θ β hk hτ hT hD ψ hψ
  have hB : n * τ + k * ((k - 1) * n) ≤ (n + k * ((k - 1) * n)) * τ := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hτ) _
  obtain ⟨c1, c2, -⟩ := Gen.withSideClauses hτ hT hD hψ hB
  have e : leaves (stepC θ k) D (rootP ψ, taut n) = (tree θ k D ψ).map fun x => (x.1, x.2 ++ taut n) := hSide θ k D (rootP ψ) (taut n)
  rw [e] at c1 c2
  have c2' := fun x (hx : x ∈ tree θ k D ψ) => c2 _ (List.mem_map_of_mem hx)
  refine ⟨fun x hx => ?_, ?_, ?_, fun x hx => (c2' x hx).2.2.2.2.2⟩
  · have := (c2' x hx).1
    simpa [stepC] using this
  · simpa [outputs] using c1
  · intro Φ hΦ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
    obtain ⟨-, -, d3, d4, d5, -⟩ := c2' x hx
    refine ⟨fun C hC => ?_, fun v => ?_⟩
    · rcases List.mem_append.1 (List.mem_dedup.1 hC) with hC | hC
      · obtain ⟨h2, h3⟩ := CountKSatRate.Leaf.mem_sideU.1 hC
        exact ⟨fun h0 => by simp [h0] at h3, by omega, (d5 C (List.mem_append_left _ h2)).2⟩
      · exact d3 C hC
    · refine (Gen.occN_out_le x v).trans ?_
      rw [occN, leafM, occ, List.filter_append, List.length_append]
      have h1 := CountKSatRate.Leaf.length_occ_sideU_le x.2 v
      have h2 : (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j := d4 v
      rw [occ] at h1 h2
      omega
end SparsificationLemma
