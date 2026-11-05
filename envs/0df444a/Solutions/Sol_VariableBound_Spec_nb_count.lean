-- Prove2me | solution 1 for VariableBound.Spec.nb_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:47.647208+00:00
-- url     : https://prove2.me/submissions/d46bd498-e1c2-4122-9453-f04a23c099b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
import Theorems.Thm_VariableBound_Spec_count_spec
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
open VariableBound
open AppVariables
open VariableBound.Spec
namespace VariableBound.Spec
theorem _root_.solution (n Δ : ℕ) (hΔ : 1 ≤ Δ) :
    2 ^ n < (2 * Δ) ^ 2 ^ ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length ∧
      ∀ a < ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length, (2 * Δ) ^ 2 ^ a ≤ 2 ^ n := by
  have h := count_spec (fun a => 2 ^ n < (2 * Δ) ^ 2 ^ a) (fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)) (Nat.log 2 n + 1)
    (fun a => by simp only [decide_eq_true_eq, not_lt])
    (fun a ha => ha.trans_le (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ a))))
    ⟨Nat.log 2 n + 1, le_rfl, by
      calc 2 ^ n < 2 ^ 2 ^ (Nat.log 2 n + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_pow_succ_log_self (by norm_num) n)
        _ ≤ (2 * Δ) ^ 2 ^ (Nat.log 2 n + 1) := Nat.pow_le_pow_left (by omega) _⟩
  exact ⟨h.1, fun a ha => not_lt.1 (h.2 a ha)⟩
end VariableBound.Spec
