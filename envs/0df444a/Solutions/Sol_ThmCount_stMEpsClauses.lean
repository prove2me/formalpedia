-- Prove2me | solution 1 for ThmCount.stMEpsClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:18.81269+00:00
-- url     : https://prove2.me/submissions/7fa344a0-95c8-401b-a90d-98db1af7367a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_Rates
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Sketch
import Mathlib.Tactic
import Definitions.Def_ThmCount_MEps
import Theorems.Thm_ThmCount_deg_le
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
import Theorems.Thm_SparsificationLemma_Cal_stDegSum
import Theorems.Thm_SparsificationLemma_Cal_stThrCal
import Theorems.Thm_SparsificationLemma_Sketch_clauses_le
import Theorems.Thm_SparsificationLemma_StepSparsify_one_le_alpha
import Theorems.Thm_SparsificationLemma_stNoTaut
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
open ThmCount
open PaperSentences
namespace ThmCount
theorem _root_.solution : StMEpsClauses := by
  refine ⟨2 * 682114, fun ε h0 h1 n φ hφ Φ hΦ => ?_⟩
  have h1' : ε ≤ 1 := by linarith
  have hα := SparsificationLemma.StepSparsify.one_le_alpha (k := 3) le_rfl h0 h1'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hΦ
  have hc := (SparsificationLemma.Sketch.clauses_le (k := 3) (by norm_num) hα (SparsificationLemma.Cal.stThrCal (SparsificationLemma.Cal.alphaC 3 ε) 3 hα) le_rfl ((SparsificationLemma.stNoTaut φ).2.1 3 n hφ) x hx).2.2
  have hs := (SparsificationLemma.Cal.stDegSum (SparsificationLemma.Cal.alphaC 3 ε) 3 hα (by norm_num)).2.1
  have hs' : ∑ j ∈ Finset.range 3, SparsificationLemma.Cal.thetaC (SparsificationLemma.Cal.alphaC 3 ε) j ≤ 2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) := by
    simpa using hs
  have hd := deg_le h0 h1
  obtain ⟨Dg, hDg⟩ : ∃ Dg, Dg = 2 + 4 * SparsificationLemma.Cal.alphaC 3 ε * (32 * SparsificationLemma.Cal.alphaC 3 ε) := ⟨_, rfl⟩
  rw [← hDg] at hs' hd
  have h2 : (SparsificationLemma.out x).length ≤ (2 * Dg + 2) * n := hc.trans (Nat.mul_le_mul_right _ (by omega))
  have h3 : ((SparsificationLemma.out x).length : ℝ) ≤ (2 * (Dg : ℝ) + 2) * n := by exact_mod_cast h2
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
  linarith
end ThmCount
