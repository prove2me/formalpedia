-- Prove2me | solution 1 for VariableBound.Net.SizeU.kind_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:20.033653+00:00
-- url     : https://prove2.me/submissions/a8367e7c-d7a0-4529-b685-3f622156161e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_VariableBound_Net_SizeU_lg_le_lg
import Theorems.Thm_ClauseBound_ParityChecks_Params_nb_mul_le
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
import Theorems.Thm_VariableBound_Ineq_binom
import Theorems.Thm_VariableBound_Ineq_nb_mul_le
import Theorems.Thm_VariableBound_Ineq_two_le_lg
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
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (hp : ParamIneq) {k n Δ m nb T μ : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hT : T ≤ (k - 1) * m)
    (hμ : μ ≤ (k - 1) * (nb + 1)) :
    lg (T.choose μ) ≤ ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ∧
      ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ≤ 3 * (k - 1 : ℕ) * (n + lg (2 * Δ)) := by
  obtain ⟨j, hj⟩ : ∃ j, j = k - 1 := ⟨_, rfl⟩
  rw [← hj] at hT hμ ⊢
  have hl := Ineq.two_le_lg hΔ
  have hn := Ineq.nb_mul_le (by omega : 1 ≤ Δ) hnb
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hjp
    · have hT0 : T = 0 := by omega
      have hμ0 : μ = 0 := by omega
      simp [hT0, hμ0, lg]
    · have h1 : 1 ≤ j * (nb + 1) := Nat.mul_pos hjp (Nat.succ_pos _)
      have h2 := Ineq.binom (t := T) hμ h1
      have hjr : (0 : ℝ) < j := by exact_mod_cast hjp
      have hnr : (0 : ℝ) < (nb : ℝ) + 1 := by positivity
      have h3 : 3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ) ≤ 3 * (m : ℝ) / (nb + 1) := by
        have hT' : (T : ℝ) ≤ j * m := by exact_mod_cast hT
        push_cast
        rw [div_le_div_iff₀ (by positivity) hnr]
        nlinarith [mul_le_mul_of_nonneg_right hT' hnr.le]
      have h4 := hp.three_m n Δ m nb hΔ hm hnb
      have h5 : lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ)) ≤ 3 * lg (2 * Δ) := by
        have h6 : lg (((2 : ℝ) * Δ) ^ 3) = 3 * lg (2 * Δ) := by unfold lg; rw [Real.logb_pow]; norm_num
        rw [← h6]
        refine lg_le_lg (by positivity) (h3.trans (h4.1.le.trans h4.2)) ?_
        have : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
        exact one_le_pow₀ (by linarith)
      have h7 : max 1 (lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ))) ≤ 3 * lg (2 * Δ) := max_le (by linarith) h5
      calc lg (T.choose μ) ≤ ((j * (nb + 1) : ℕ) : ℝ) * max 1 (lg (3 * (T : ℝ) / ((j * (nb + 1) : ℕ) : ℝ))) := h2
        _ ≤ ((j * (nb + 1) : ℕ) : ℝ) * (3 * lg (2 * Δ)) := mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg _)
        _ = (j : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) := by push_cast; ring
  · have : (j : ℝ) * ((nb : ℝ) * lg (2 * Δ)) ≤ j * n := mul_le_mul_of_nonneg_left hn hj0
    nlinarith
end VariableBound.Net.SizeU
