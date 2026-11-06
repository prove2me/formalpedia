-- Prove2me | solution 1 for SparsificationLemma.Geo.stTauE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:50:03.027991+00:00
-- url     : https://prove2.me/submissions/91f46a5f-6b1c-4153-a79f-2701dce2aec4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Geo_Eps
import Theorems.Thm_SparsificationLemma_Geo_works_of_cube
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
open SparsificationLemma SparsificationLemma.Geo
open UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution : StTauE := by
  intro k ε hk h0 h1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hq0 : 0 ≤ (8 * (k : ℚ) / ε) ^ 3 := by positivity
  have hloQ : (8 * (k : ℚ) / ε) ^ 3 ≤ (tauE k ε : ℚ) := Nat.le_ceil _
  have hhiQ : (tauE k ε : ℚ) < (8 * (k : ℚ) / ε) ^ 3 + 1 := Nat.ceil_lt_add_one hq0
  have hlo : (8 * (k : ℝ) / (ε : ℝ)) ^ 3 ≤ (tauE k ε : ℝ) := by exact_mod_cast hloQ
  have hhi' : (tauE k ε : ℝ) < (8 * (k : ℝ) / (ε : ℝ)) ^ 3 + 1 := by exact_mod_cast hhiQ
  have hXk : (k : ℝ) = (ε : ℝ) * (8 * (k : ℝ) / (ε : ℝ)) / 8 := by field_simp
  have h9 : 9 * (k : ℝ) / (ε : ℝ) = 9 * (8 * (k : ℝ) / (ε : ℝ)) / 8 := by ring
  have h8k : 8 * (k : ℝ) ≤ 8 * (k : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; nlinarith
  rw [h9]
  generalize 8 * (k : ℝ) / (ε : ℝ) = X at *
  have hX8 : 8 ≤ X := by linarith
  have hX3 : 64 * X ≤ X ^ 3 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by nlinarith : (0 : ℝ) ≤ X ^ 2 - 64)]
  have hhi : (tauE k ε : ℝ) ≤ (9 * X / 8) ^ 3 := by nlinarith
  refine ⟨?_, ?_, hhi⟩
  · have : ((8 * k : ℕ) : ℝ) ≤ (tauE k ε : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have := works_of_cube hkR h0R h1R hXk hlo hhi
    simpa [bsumU] using this
end SparsificationLemma.Geo
