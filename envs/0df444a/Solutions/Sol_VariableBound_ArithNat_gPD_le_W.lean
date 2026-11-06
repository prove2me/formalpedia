-- Prove2me | solution 1 for VariableBound.ArithNat.gPD_le_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:55.955405+00:00
-- url     : https://prove2.me/submissions/21b2e2e5-d07e-4df7-b0b1-a08351d62068

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNat
import Theorems.Thm_VariableBound_ArithNat_gPD_le
import Theorems.Thm_VariableBound_ArithNat_g_le_n
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_size_n_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (hB : StBounds) (hβ : 1 ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) := by
  have hK1 : 1 ≤ K := by omega
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have h := gPD_le hB hβ (hK1.trans hKn) (g_le_n hK hn17)
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  refine h.trans ?_
  unfold WofU GD
  generalize K.size = Y at hz hY
  generalize n.size = z at hz
  generalize 2 ^ β = D
  have hb1 : 1 ≤ β + 3 := by omega
  generalize β + 3 = b at hb1
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have a1 : b ≤ b ^ 2 * Y := hbb.trans (Nat.le_mul_of_pos_right _ hY)
  have a2 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hb1)
  have h2 : 842 * b + 4 * z ≤ (842 + 68 * C₀) * (b ^ 2 * Y) := by
    calc 842 * b + 4 * z ≤ 842 * (b ^ 2 * Y) + 4 * (17 * C₀ * (b ^ 2 * Y)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ a1) (Nat.mul_le_mul_left _ (hz.trans (Nat.mul_le_mul_left _ a2)))
      _ = (842 + 68 * C₀) * (b ^ 2 * Y) := by ring
  calc n * D * (842 * b + 4 * z) ≤ n * D * ((842 + 68 * C₀) * (b ^ 2 * Y)) := Nat.mul_le_mul_left _ h2
    _ = (842 + 68 * C₀) * (b ^ 2 * D * Y * n) := by ring
end VariableBound.ArithNat
