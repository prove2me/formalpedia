-- Prove2me | solution 1 for UniformInK.stMasterU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:34:20.437634+00:00
-- url     : https://prove2.me/submissions/dddffab9-943f-4c93-8bf6-58b23115090d

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
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_pow_le
import Theorems.Thm_ClauseBound_Alg_TopArith_size_le_two_logb
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
theorem _root_.solution : StMasterU := by
  intro β K C₀ e hbD hK he h6
  have hY : (K.size : ℝ) ≤ 2 * Real.logb 2 K := size_le_two_logb K hK
  have hq := logb_pow_le K (2 * C₀ + 2) hK
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hA : (A1U C₀ : ℝ) = 1 + (((2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2) : ℕ) : ℝ) := by
    unfold A1U; push_cast; ring
  rw [hA]
  generalize (((2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2) : ℕ) : ℝ) = F at hq ⊢
  generalize Real.logb 2 K = y at he hy1 hY hq
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have hb : ((β + 3 : ℕ) : ℝ) ≤ ((2 ^ β : ℕ) : ℝ) := by exact_mod_cast hbD
  have h6r : ((2 ^ β : ℕ) : ℝ) ^ 6 ≤ (K : ℝ) := by exact_mod_cast h6
  have hW0 : ((WofU β K : ℕ) : ℝ) = ((β + 3 : ℕ) : ℝ) ^ 2 * ((2 ^ β : ℕ) : ℝ) * (K.size : ℝ) := by
    unfold WofU; push_cast; ring
  rw [hW0]
  have hb0 : (0 : ℝ) ≤ ((β + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ β : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ (K.size : ℝ) := Nat.cast_nonneg _
  generalize ((β + 3 : ℕ) : ℝ) = b at hb hb0 ⊢
  generalize ((2 ^ β : ℕ) : ℝ) = D at hb h6r hD0 ⊢
  generalize (K.size : ℝ) = Y at hY hY0 ⊢
  generalize (K : ℝ) = κ at h6r hq ⊢
  have hsq : 2 * D ^ 3 * y ^ (C₀ + 1) ≤ (D ^ 3) ^ 2 + (y ^ (C₀ + 1)) ^ 2 := by
    nlinarith [sq_nonneg (D ^ 3 - y ^ (C₀ + 1))]
  calc b ^ 2 * D * Y ≤ D ^ 2 * D * (2 * y) := by gcongr
    _ = 2 * D ^ 3 * y * 1 := by ring
    _ ≤ 2 * D ^ 3 * y * (e * y ^ C₀) := mul_le_mul_of_nonneg_left h1e (by positivity)
    _ = e * (2 * D ^ 3 * y ^ (C₀ + 1)) := by ring
    _ ≤ e * ((D ^ 3) ^ 2 + (y ^ (C₀ + 1)) ^ 2) := mul_le_mul_of_nonneg_left hsq he0.le
    _ = e * (D ^ 6 + y ^ (2 * C₀ + 2)) := by ring
    _ ≤ e * (κ + F * κ) := mul_le_mul_of_nonneg_left (add_le_add h6r hq) he0.le
    _ = (1 + F) * κ * e := by ring
end UniformInK
