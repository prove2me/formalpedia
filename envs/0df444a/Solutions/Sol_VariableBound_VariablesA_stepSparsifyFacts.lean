-- Prove2me | solution 1 for VariableBound.VariablesA.stepSparsifyFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:55.919969+00:00
-- url     : https://prove2.me/submissions/dbf15087-df44-4d3a-a690-b39d83824d9a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
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
import Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
import Theorems.Thm_VariableBound_VariablesA_e_ge_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_lg_lt
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
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.VariablesA
theorem _root_.solution : StepSparsifyFactsStmt := by
  intro Idx _ S e C₀ Q k n l hl hk hk4
  have hC : (1 : ℝ) ≤ C₀ := by exact_mod_cast one_le_C₀ Q
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hy : 1 ≤ MainTheoremForms.lg n := (one_le_pow₀ hk').trans hk4
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have he0 := e_pos Q l
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    have := lg_lt Q hl
    linarith
  · have h1 : MainTheoremForms.lg (k / e l) = MainTheoremForms.lg k - MainTheoremForms.lg (e l) := Real.logb_div (by positivity) he0.ne'
    have h2 : 4 * MainTheoremForms.lg k ≤ MainTheoremForms.lg (MainTheoremForms.lg n) := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk4
      rw [Real.logb_pow] at this
      simpa [MainTheoremForms.lg] using this
    have h3 : -((C₀ : ℝ) * MainTheoremForms.lg (MainTheoremForms.lg n)) ≤ MainTheoremForms.lg (e l) := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (e_ge_n Q hl)
      rw [one_div, Real.logb_inv, Real.logb_pow] at this
      simpa [MainTheoremForms.lg] using this
    rw [h1]
    linarith
end VariableBound.VariablesA
