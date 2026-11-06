-- Prove2me | solution 1 for SplitCount.stStepOneFor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:27.572204+00:00
-- url     : https://prove2.me/submissions/0de8475b-5d1f-4906-a7da-5c7b0f9151bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_Occ_Main
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_StepOne
import Theorems.Thm_GraphProblems_cntN_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_nat_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_bind_runs
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Occ_stCountOcc
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_cntN_le
import Theorems.Thm_SplitCount_poly_le
import Theorems.Thm_SplitCount_size_nat_le
import Theorems.Thm_SplitCount_size_unary
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.snd
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
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
namespace SplitCount
theorem _root_.solution : StStepOneFor := by
  intro Cnt δ' A hδ' hC
  refine ⟨6 + 1 + A * 1 ^ A + 1 * A, fun n Φ h3 hb => ?_⟩
  obtain ⟨T, r, hT⟩ := hC Φ h3
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), Φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = n + size Φ + 1 := ⟨_, rfl⟩
  rw [← ha, ← hs]
  -- «Z·2^{n'}» is the number of satisfying assignments
  have hv : timesFree (a, ((Eight.numSat Φ : ℕ) : ℤ)) = cntN n Φ := by
    rw [ha, stCountOcc n Φ hb]
    simp [timesFree]
  have r1 : (Stepped.mapIn Prod.snd Cnt).Runs a T (A * size Φ ^ A) ((Eight.numSat Φ : ℕ) : ℤ) := Stepped.mapIn_runs (by rw [ha]; exact r)
  have r2 := Stepped.ofFun_runs timesFree (a, ((Eight.numSat Φ : ℕ) : ℤ))
  rw [hv] at r2
  have hc2 : cntN n Φ < 2 ^ (n + 1) := (cntN_le n Φ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz2 : Eight.numSat Φ < 2 ^ (n + 1) := by
    refine lt_of_le_of_lt ?_ hc2
    rw [stCountOcc n Φ hb]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have s1 : size a ≤ 2 * s := by
    have := size_unary n
    rw [ha, size_prod]
    show size (List.replicate n ()) + size Φ ≤ _
    omega
  have s2 : size (cntN n Φ) ≤ s + 1 := by have := size_nat_le hc2; omega
  have s3 : size ((Eight.numSat Φ : ℕ) : ℤ) ≤ s + 1 := by
    have := size_nat_le hz2
    rw [size_nat] at this
    rw [size_int, Int.natAbs_natCast]
    omega
  have s4 : A * size Φ ^ A ≤ A * (1 * s ^ 1) ^ A := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [one_mul, pow_one]; omega) A)
  refine ⟨T + 1 + 1, (Stepped.bind_runs r1 r2).mono le_rfl (poly_le (by omega) ?_), ?_⟩
  · have sp : size (a, ((Eight.numSat Φ : ℕ) : ℤ)) = size a + size ((Eight.numSat Φ : ℕ) : ℤ) := size_prod _
    rw [sp, pow_one]
    rw [pow_one] at s4
    omega
  · have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ' * Φ.length) := Real.one_le_rpow one_le_two (by positivity)
    have hcA : (A : ℝ) + 2 ≤ ((6 + 1 + A * 1 ^ A + 1 * A : ℕ) : ℝ) := by
      have : A + 2 ≤ 6 + 1 + A * 1 ^ A + 1 * A := by rw [one_pow]; omega
      exact_mod_cast this
    calc ((T + 1 + 1 : ℕ) : ℝ) = (T : ℝ) + 2 := by push_cast; ring
      _ ≤ (A : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) + 2 * (2 : ℝ) ^ (δ' * Φ.length) := by linarith
      _ = ((A : ℝ) + 2) * (2 : ℝ) ^ (δ' * Φ.length) := by ring
      _ ≤ ((6 + 1 + A * 1 ^ A + 1 * A : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) := mul_le_mul_of_nonneg_right hcA (by positivity)
end SplitCount
