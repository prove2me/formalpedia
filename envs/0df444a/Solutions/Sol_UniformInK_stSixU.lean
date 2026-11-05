-- Prove2me | solution 1 for UniformInK.stSixU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:34:30.934185+00:00
-- url     : https://prove2.me/submissions/bdf74540-d017-4591-962d-1bb446ac6aa3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_ParityChecks_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_UniformInK_Top_ArithMaster
import Theorems.Thm_ClauseBound_ParityChecks_Params_mul_clog_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
open ClauseBound.Alg.TopArith
namespace UniformInK
theorem _root_.solution : StSixU := by
  intro D c K n C₀ hc hn hlt hD hℓ
  have hC₀ : 1 ≤ C₀ := by
    rcases Nat.eq_zero_or_pos C₀ with h | h
    · subst h
      simp at hlt
      omega
    · exact h
  have hA : 1 ≤ 102 * C₀ * c := Nat.mul_pos (by omega) hc
  have hcl := ClauseBound.ParityChecks.Params.mul_clog_le (102 * C₀ * c) (Nat.log 2 n) hA hℓ
  have hpow : (D ^ 6) ^ (17 * C₀) < K ^ (17 * C₀) :=
    calc (D ^ 6) ^ (17 * C₀) = D ^ (102 * C₀) := by rw [← pow_mul]; congr 1; ring
      _ ≤ ((Nat.log 2 n + 1) ^ c) ^ (102 * C₀) := Nat.pow_le_pow_left hD _
      _ ≤ ((2 ^ Nat.clog 2 (Nat.log 2 n + 1)) ^ c) ^ (102 * C₀) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _) _
      _ = 2 ^ (102 * C₀ * c * Nat.clog 2 (Nat.log 2 n + 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) hcl
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
      _ < K ^ (17 * C₀) := hlt
  exact (lt_of_pow_lt_pow_left₀ _ (Nat.zero_le K) hpow).le
end UniformInK
