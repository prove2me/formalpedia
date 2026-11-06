-- Prove2me | solution 1 for SparsificationLemma.Mach.length_encIn_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:35:58.1002+00:00
-- url     : https://prove2.me/submissions/19f57762-787d-4567-bb1d-3964e145643e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    (encIn s 3 φ).length + 2 ^ 3 ≤ (s + 412) * (n + 1) ^ 4 := by
  have h1 := DecodeK.length_enc_succ_le h3
  have h2 : (n + 2) ^ 4 ≤ (2 * (n + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : (2 * (n + 1)) ^ 4 = 16 * (n + 1) ^ 4 := by ring
  have h4 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h5 : (encIn s 3 φ).length = s + 5 + (SatK.enc 3 φ).length := by
    simp only [encIn, SatM.enc, List.length_append, List.length_replicate, List.length_cons]; omega
  have h6 : (s + 412) * (n + 1) ^ 4 = s * (n + 1) ^ 4 + 412 * (n + 1) ^ 4 := by ring
  have h7 : s ≤ s * (n + 1) ^ 4 := Nat.le_mul_of_pos_right _ h4
  norm_num at h1
  omega
end SparsificationLemma.Mach
