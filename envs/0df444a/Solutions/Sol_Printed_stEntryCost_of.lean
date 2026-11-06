-- Prove2me | solution 1 for Printed.stEntryCost_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:50:07.117852+00:00
-- url     : https://prove2.me/submissions/7a15f170-40e5-40be-97f6-ce480f1fe01e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_size_netInput_le
import Theorems.Thm_Printed_abs_display_lt
import Theorems.Thm_Printed_poly_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
import Theorems.Thm_Eight_ViaGrouping_tableM_display
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_tableQ_close
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
import Theorems.Thm_QueryMachines_stClose
import Theorems.Thm_QueryMachines_stSlowDown
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hTL : StToLists) : StEntryCost := by
  intro K g
  obtain ⟨c₁, h1, hc₁⟩ := tableM_display K g
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * g ^ 2 + 6 * g + 6 := ⟨_, rfl⟩
  refine ⟨(D + 2 * size g + 8) + c₁ * (D + 1) ^ c₁ + c₁, fun hK0 hg N P B τ hN hτ x hx L hL hG1 hY γ Θ hΘ => ?_⟩
  have hnet := asked_isNetworkP N hN
  obtain ⟨e1, e2, -⟩ := hTL K L γ Θ hΘ
  have hΘ' : ∀ γ', γ' ≠ γ → ((fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ').length = L := fun γ' hne => by
    simp only [if_neg hne]
    exact e2 γ' hne
  have hγ : (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ = [] := if_pos rfl
  obtain ⟨hrun, -⟩ := hc₁ hK0 _ _ _ N P B 1 _ hnet x hx L hL hG1 hY γ _ hΘ' hγ
  refine ⟨?_, abs_display_lt hnet hK0 hg x L hG1 hY γ _ hΘ'⟩
  rw [e1]
  rw [← tableQ_close] at hrun
  have hw := stSlowDown _ _ _ _ _ _ _ _ _ τ _ hτ ((stClose _ _ _ _ _ _ _ _ _ _).1 hrun)
  refine hw.mono ?_ ?_
  · rw [Nat.mul_one]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · have hs := size_netInput_le N hN
    rw [← hD] at hs
    have hP := hN.P_pos
    obtain ⟨X, hX⟩ : ∃ X, X = P + B := ⟨_, rfl⟩
    rw [← hX] at hs ⊢
    have a1 : size (netInput N P B) + 2 * size g + 4 * P + B + 4 ≤ (D + 2 * size g + 8) * X := by
      have : (D + 2 * size g + 8) * X = D * X + 2 * size g * X + 8 * X := by ring
      have h2 : 2 * size g * 1 ≤ 2 * size g * X := Nat.mul_le_mul_left _ (by omega)
      omega
    have a2 : c₁ * (size (netInput N P B) + P + B) ^ c₁ ≤ c₁ * (D + 1) ^ c₁ * X ^ c₁ := by
      rw [Nat.mul_assoc, ← Nat.mul_pow]
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
      have : (D + 1) * X = D * X + X := by ring
      omega
    exact (Nat.add_le_add a1 a2).trans (poly_le (by omega) (by omega) (by omega) (by omega))
end Printed
