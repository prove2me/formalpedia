-- Prove2me | solution 1 for StepSparsify.stCalLeaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:50.707047+00:00
-- url     : https://prove2.me/submissions/d3f5a7a9-b86d-4188-9863-2b8591f687dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepSparsify_CalLeaves
import Theorems.Thm_StepSparsify_leaves_eq_of_le
import Theorems.Thm_StepSparsify_yC_mono
import Theorems.Thm_StepSparsify_yC_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_SparsificationLemma_Cal_factI
import Theorems.Thm_SparsificationLemma_Cal_factIIIy
import Theorems.Thm_SparsificationLemma_Cal_gen
import Theorems.Thm_StepSparsify_le_alphaS
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
open StepSparsify
open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma
namespace StepSparsify
theorem _root_.solution : StCalLeaves := by
  intro k n s D ψ hk hD hψ
  have hα : 1 ≤ alphaS k s := le_trans (by norm_num) (le_alphaS k s).1
  have e : tree (thCal k s) k D ψ = tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ :=
    leaves_eq_of_le _ _ D _ hD (Cal.factI (alphaS k s) k n ψ hα hk hψ)
  rw [e]
  obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
  · have h := (Cal.gen hα hk hψ).2.1
    rw [outputs, List.length_map] at h
    simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_div, Nat.zero_add, sum_range_one, Nat.choose_zero_right] at h
    exact h.trans Nat.one_le_two_pow
  · have h1 := Cal.factIIIy (alphaS k s) k n ψ hα hk2 hψ
    have hy : Cal.yC k (alphaS k s) ≤ 1 / 2 ^ s := (yC_mono _ hk (le_max_left k 3) hα).trans (yC_le k s)
    have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
    have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
    have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
      rw [one_div, inv_mul_le_iff₀ (by positivity)]
      exact h3
    have h5 : ((tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ).length : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
      calc ((tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ).length : ℝ) ≤ (2 : ℝ) ^ (Cal.yC k (alphaS k s) * (n : ℝ)) := h1
        _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ((mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg n)).trans h4)
        _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    exact_mod_cast h5
end StepSparsify
