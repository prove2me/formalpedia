-- Prove2me | solution 1 for StepSparsify.stCalNumbers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:26.410969+00:00
-- url     : https://prove2.me/submissions/2b5b5a61-e21c-4b72-a259-a77bb8bf7af7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_UniformInK_Top_Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_StepSparsify_CalNumbers
import Theorems.Thm_StepSparsify_le_alphaS
import Theorems.Thm_StepSparsify_alpha_le
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
import Theorems.Thm_SparsificationLemma_Cal_betaC_zero
import Theorems.Thm_SparsificationLemma_Cal_factIV
import Theorems.Thm_SparsificationLemma_Cal_stDegSum
import Theorems.Thm_SparsificationLemma_Cal_sum_range_betaC
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
import Theorems.Thm_UniformInK_Leaves_sq_le_of_s0U_le
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
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
namespace StepSparsify
theorem _root_.solution : StCalNumbers := by
  intro k s hk hs
  obtain ⟨a2, a3⟩ := le_alphaS k s
  have hq := alpha_le hk (Leaves.sq_le_of_s0U_le hs)
  have hα : 1 ≤ alphaS k s := by omega
  have hT : 18 ≤ tauOf s ^ 2 := by
    calc 18 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ ((4 * s + 17) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = tauOf s ^ 2 := by rw [tauOf, ← pow_mul]
  have hb : bsumU (tauOf s) k = (tauOf s ^ 2) ^ k := by rw [bsumU, pow_mul]
  rw [← Leaves.bsumU_tauOf, hb]
  generalize tauOf s ^ 2 = T at hq hT
  refine ⟨hα, (Nat.pow_le_pow_left (le_max_left k 3) 2).trans a3, ?_, ?_⟩
  · obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
    · simp [Cal.betaC_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [Cal.sum_range_betaC _ hk]
      calc ∑ c ∈ Ico 1 (j + 2), Cal.betaC (alphaS (j + 2) s) c ≤ 4 * (32 * alphaS (j + 2) s) ^ j := Cal.factIV _ _ hα hk2
        _ ≤ 4 * T ^ j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq j)
        _ ≤ T ^ 2 * T ^ j := Nat.mul_le_mul_right _ (by nlinarith)
        _ = T ^ (j + 2) := by ring
  · obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
    · simp only [lcCal, thCal, sum_range_one, Cal.thetaC, pow_one]
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      obtain ⟨-, d2, d3⟩ := Cal.stDegSum (alphaS (j + 2) s) (j + 2) hα hk2
      rw [Nat.add_sub_cancel] at d2 d3
      rw [show j + 2 - 1 = j + 1 by omega] at d3
      have h1 : (32 * alphaS (j + 2) s) ^ (j + 1) ≤ T ^ (j + 1) := Nat.pow_le_pow_left hq _
      have h2 : T ≤ T ^ (j + 1) := by
        calc T = T ^ 1 := (pow_one T).symm
          _ ≤ T ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 * T ^ (j + 1) ≤ T ^ (j + 2) := by
        rw [pow_succ T (j + 1), Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      rw [lcCal, thCal]
      omega
end StepSparsify
