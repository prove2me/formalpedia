-- Prove2me | solution 1 for PaddedDescent.F.stA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:27.609261+00:00
-- url     : https://prove2.me/submissions/5bf6fcc0-61cc-4666-a6a0-3318865960c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_ArithSched
import Definitions.Def_PaddedDescent_F_ArithFits
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Definitions.Def_PaddedDescent_F_ArithMark
import Definitions.Def_PaddedDescent_F_ArithA
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
import Theorems.Thm_PaddedDescent_F_Arith_Qmof_lt
import Theorems.Thm_PaddedDescent_F_Arith_Ytop_ge
import Theorems.Thm_PaddedDescent_F_Arith_Zof_ge
import Theorems.Thm_PaddedDescent_F_Arith_Zof_le_Qmof
import Theorems.Thm_PaddedDescent_F_Arith_chain_schedL
import Theorems.Thm_PaddedDescent_F_Arith_clauses_le
import Theorems.Thm_PaddedDescent_F_Arith_exponents_le
import Theorems.Thm_PaddedDescent_F_Arith_fits_of_inv
import Theorems.Thm_PaddedDescent_F_Arith_hundred_Ytop_le
import Theorems.Thm_PaddedDescent_F_Arith_inv_at_top
import Theorems.Thm_PaddedDescent_F_Arith_layLen_le
import Theorems.Thm_PaddedDescent_F_Arith_layers_last
import Theorems.Thm_PaddedDescent_F_Arith_nProf_le
import Theorems.Thm_PaddedDescent_F_Arith_poly_le
import Theorems.Thm_PaddedDescent_F_Arith_schedLen_le
import Theorems.Thm_PaddedDescent_F_Arith_top_col
import Theorems.Thm_PaddedDescent_F_Arith_top_lab
import Theorems.Thm_PaddedDescent_F_Arith_top_st
import Theorems.Thm_PaddedDescent_F_Arith_top_tab
import Theorems.Thm_PaddedDescent_Kseq_ge
import Theorems.Thm_PaddedDescent_Ytop_sOf_pow_le
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
open PaddedDescent PaddedDescent.F
open Arith
namespace PaddedDescent.F
theorem _root_.solution : StA := by
  intro k n F Δ hs hF hk hΔ
  have hY : Ytop (sOf n) ^ 6 ≤ n := Ytop_sOf_pow_le (by norm_num) hs
  have hF' : 2 ^ (8 * Xof (sOf n) n) ≤ F := hF
  have hE := exponents_le hY
  have hn : 6 ≤ n := by
    have h1 := hundred_Ytop_le hY
    have h2 := Ytop_ge (sOf n)
    omega
  have hfits := fits_of_inv (F := F) (e := 8 * Xof (sOf n) n) (Lw := 2 * Lof (sOf n) n) (Zof_ge (sOf n))
    (Zof_le_Qmof k (sOf n) n) (Qmof_lt hk hY) (poly_le hk hY) (by omega)
    (by
      have e : Lof (sOf n) n * (2 * Kseq (depthOf (sOf n)) ^ 2) = 2 * (Lof (sOf n) n * Kseq (depthOf (sOf n)) ^ 2) := by ring
      omega)
    (by omega) (by omega) hF' (depthOf (sOf n)) le_rfl _ _ _ (inv_at_top hk hΔ hY)
  refine ⟨?_, schedLen_le hs (by norm_num) hF⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, layLen_le hs (by norm_num) hF hk hΔ, layers_last hΔ hn, by positivity, le_rfl, clauses_le hΔ _⟩ <;> simp only [List.length_replicate]
  · exact chain_schedL _
  · exact le_trans (by norm_num) (Kseq_ge _)
  · exact top_col hY hF'
  · exact top_st hΔ hY hF'
  · exact top_lab hΔ hY hF'
  · exact top_tab hk hΔ hY hF'
  · exact hfits
  · exact nProf_le hs (by norm_num) hF hΔ
end PaddedDescent.F
