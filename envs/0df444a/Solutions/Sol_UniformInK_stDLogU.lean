-- Prove2me | solution 1 for UniformInK.stDLogU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:11.039661+00:00
-- url     : https://prove2.me/submissions/4a09dbaf-60d6-4478-b104-f4d2867b6335

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
import Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_le_of_le_pow
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
theorem _root_.solution : StDLogU := by
  intro K n s C C₀ k e hK hKn he h2
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hy : Real.logb 2 K ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) :=
    logb_le_of_le_pow K (Nat.log 2 n + 1) (by omega) (hKn.trans (Nat.lt_pow_succ_log_self (by norm_num) n).le)
  have hL : 2 ≤ Nat.log 2 n + 1 := by
    have := Nat.log_pos (b := 2) (by norm_num) (hK.trans hKn)
    omega
  have hLr : (2 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hL
  have hfin : ((2 ^ betaU k s : ℕ) : ℝ) ≤ (((Nat.log 2 n + 1) ^ (aU C C₀ * k) : ℕ) : ℝ) := by
    rw [Nat.cast_pow (Nat.log 2 n + 1)]
    generalize ((Nat.log 2 n + 1 : ℕ) : ℝ) = L at hy hLr ⊢
    generalize Real.logb 2 K = y at he hy1 hy
    have hy0 : 0 < y := by linarith
    have hyC : 0 < y ^ C₀ := by positivity
    have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
    have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
    have h2e : 2 / e ≤ 2 * y ^ C₀ := by
      rw [div_le_iff₀ he0]
      nlinarith
    have hs : (2 : ℝ) ^ s ≤ (2 * y ^ C₀) ^ C := h2.trans (pow_le_pow_left₀ (by positivity) h2e C)
    have hs' : (2 : ℝ) ^ s ≤ (L * L ^ C₀) ^ C := hs.trans (by gcongr)
    have eβ : betaU k s = s * (8 * k) + 34 * k := by unfold betaU; ring
    calc ((2 ^ betaU k s : ℕ) : ℝ) = ((2 : ℝ) ^ s) ^ (8 * k) * 2 ^ (34 * k) := by
          rw [eβ]; push_cast; rw [pow_add, pow_mul]
      _ ≤ ((L * L ^ C₀) ^ C) ^ (8 * k) * L ^ (34 * k) := by gcongr
      _ = L ^ (aU C C₀ * k) := by unfold aU; ring
  exact_mod_cast hfin
end UniformInK
