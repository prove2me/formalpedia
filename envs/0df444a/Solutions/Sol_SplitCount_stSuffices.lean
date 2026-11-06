-- Prove2me | solution 1 for SplitCount.stSuffices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:48.343804+00:00
-- url     : https://prove2.me/submissions/da7b1c93-5073-410b-9a1d-60dc4b67bc5d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Suffices
import Theorems.Thm_SplitCount_engineBy_runs
import Theorems.Thm_GraphProblems_exists_toN
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
import Theorems.Thm_WidthK_InvK_step
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
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ
namespace SplitCount
theorem _root_.solution : StSuffices := by
  intro k hk δ hδ step Dd Bl Sk hsp D δ' A hδ' hδB hD
  obtain ⟨c, h⟩ := engineBy_runs hδ hsp hδ' hδB hD
  refine ⟨c * (k * 2 ^ k + 1) ^ c + (k + 1) * c, fun N ψ hψ hnd => ?_⟩
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN fun C hC => (hψ C hC).2
  have h3 : SatK.IsKCNF k φ := by
    refine ⟨fun C hC => ?_, List.Nodup.of_map _ hnd⟩
    have := (hψ (C.map fun l => (l.1.val, l.2)) (List.mem_map_of_mem hC)).1
    simpa using this
  have hlen := DecodeK.length_enc k φ
  have hm : φ.length ≤ (SatK.enc k φ).length + 1 := by
    have hB : 0 < k * (Nat.log2 (2 * N) + 1) := Nat.mul_pos hk (by omega)
    have := Nat.le_mul_of_pos_right φ.length hB
    omega
  obtain ⟨T, hr, hT⟩ := h N (Decode.toN φ) ((SatK.enc k φ).length + 1) hψ (by omega) (by rw [Decode.length_toN]; exact hm) (by omega)
  refine ⟨T, hr.mono le_rfl ?_, hT.trans ?_⟩
  · have hl := DecodeK.length_enc_succ_le h3
    calc c * ((SatK.enc k φ).length + 1) ^ c ≤ c * ((k * 2 ^ k + 1) * (N + 2) ^ (k + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
      _ = (c * (k * 2 ^ k + 1) ^ c) * (N + 2) ^ ((k + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ (c * (k * 2 ^ k + 1) ^ c + (k + 1) * c) * (N + 2) ^ (c * (k * 2 ^ k + 1) ^ c + (k + 1) * c) :=
          Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : 1 ≤ (k * 2 ^ k + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have h2 : c ≤ c * (k * 2 ^ k + 1) ^ c + (k + 1) * c := (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
    exact_mod_cast h2
end SplitCount
