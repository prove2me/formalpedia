-- Prove2me | solution 1 for VariableBound.Net.SizeSmall.U_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:56:51.435947+00:00
-- url     : https://prove2.me/submissions/d5cc38e5-a683-4c96-abf6-7b08a34443ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
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
import Theorems.Thm_VariableBound_Net_SizeP_cw_le
import Theorems.Thm_VariableBound_Net_Tests_U_eq
import Theorems.Thm_VariableBound_Net_Tests_capD_eq
import Theorems.Thm_VariableBound_Net_Tests_card_kind_one
import Theorems.Thm_VariableBound_Net_Tests_card_kind_zero
import Theorems.Thm_VariableBound_Net_Tests_sum_length_tst_le
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
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}
namespace VariableBound.Net.SizeSmall
theorem _root_.solution {ψ : Fml} (hW : WfD k n (ψ, [])) (y : ℕ) (fl : Bool) : (netDN g (ctx g n (ψ, []) y fl)).U ≤ 2 * (k - 1) * ψ.length := by
  have h0 := Tests.sum_length_tst_le (g := g) hW 0
  have h1 := Tests.sum_length_tst_le (g := g) hW 1
  rw [Tests.card_kind_zero hW] at h0
  rw [Tests.card_kind_one hW] at h1
  simp only [List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at h0 h1
  have hc : ∀ a b, capD g n (ψ, []) y a b ≤ (tst g n (ψ, []) a b 0).length + (tst g n (ψ, []) a b 1).length := by
    intro a b
    rw [Tests.capD_eq, sum_range_succ, sum_range_succ, sum_range_zero, Nat.zero_add]
    exact Nat.add_le_add (SizeP.cw_le _ _) (SizeP.cw_le _ _)
  rw [Tests.U_eq, Nat.mul_assoc]
  refine Nat.mul_le_mul_left 2 ?_
  refine (sum_le_sum fun b _ => sum_le_sum fun a _ => hc a b).trans ?_
  simp only [sum_add_distrib]
  omega
end VariableBound.Net.SizeSmall
