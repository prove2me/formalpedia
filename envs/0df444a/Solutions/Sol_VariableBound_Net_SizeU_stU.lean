-- Prove2me | solution 1 for VariableBound.Net.SizeU.stU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:09.167607+00:00
-- url     : https://prove2.me/submissions/5c264f8a-28c5-4539-9b27-fc318827d81c

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
import Theorems.Thm_VariableBound_Net_SizeU_totP_eq
import Theorems.Thm_VariableBound_Net_SizeU_adm_spec
import Theorems.Thm_VariableBound_Net_SizeU_tests_le
import Theorems.Thm_VariableBound_Net_SizeU_one_le_k
import Theorems.Thm_VariableBound_Net_SizeU_kind_zero_le
import Theorems.Thm_VariableBound_Net_SizeU_kind_one_le
import Theorems.Thm_VariableBound_Net_SizeU_sum_cw_le
import Theorems.Thm_VariableBound_Net_SizeU_two_mul_pairs_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
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
import Theorems.Thm_VariableBound_Net_Tests_U_eq
import Theorems.Thm_VariableBound_Net_Tests_capD_eq
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
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (hp : ParamIneq) : StU := by
  intro k g n Δ nb M D fl y _ hS hadm
  obtain ⟨h0, h1, h2⟩ := adm_spec hadm
  have hk : 1 ≤ k := one_le_k hS.wf (Nat.zero_lt_of_lt hS.lt_m)
  obtain ⟨hT0, hT1, hI⟩ := tests_le g hk hS.wf hS.row
  have hμ0 : ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b 0 ≤ (k - 1) * (nb + 1) := by
    rw [← totP_eq]
    exact ((h2 0 (by norm_num)).1).trans (Nat.mul_le_mul_left _ h0)
  have hμ1 : ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b 1 ≤ k * M := by
    rw [← totP_eq]
    refine ((h2 1 (by norm_num)).1).trans ?_
    rw [Nat.sub_add_cancel hk]
    exact Nat.mul_le_mul_left _ h1
  have c0 := sum_cw_le g (fun a b => (tst g n D a b 0).length) (fun a b => mu g D y a b 0) (h2 0 (by norm_num)).2
  have c1 := sum_cw_le g (fun a b => (tst g n D a b 1).length) (fun a b => mu g D y a b 1) (h2 1 (by norm_num)).2
  have k0 := kind_zero_le hp hS.two hS.m_le hS.isNb hT0 hμ0
  have k1 := kind_one_le hp hS.two hS.lt_m hS.m_le hS.isNb hk hS.r_le hS.one_le hI hT1 hμ1
  have hg : 2 * ((∑ b ∈ range g, b : ℕ) : ℝ) ≤ (g : ℝ) ^ 2 := by exact_mod_cast two_mul_pairs_le g
  have hU : ((netDN g (ctx g n D y fl)).U : ℝ) =
      2 * (((∑ b ∈ range g, ∑ a ∈ range b, cw (tst g n D a b 0).length (mu g D y a b 0) : ℕ) : ℝ) +
        ((∑ b ∈ range g, ∑ a ∈ range b, cw (tst g n D a b 1).length (mu g D y a b 1) : ℕ) : ℝ)) := by
    rw [Tests.U_eq]
    simp only [Tests.capD_eq, sum_range_succ, sum_range_zero, Nat.zero_add, sum_add_distrib]
    push_cast
    ring
  rw [hU]
  linarith [k0.1, k0.2, k1.1, k1.2]
end VariableBound.Net.SizeU
