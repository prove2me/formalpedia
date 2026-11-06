-- Prove2me | solution 1 for Printed.asked_isNetworkP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:04.967557+00:00
-- url     : https://prove2.me/submissions/1b45aabc-39fb-4282-87f7-e49d2bebd6d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Printed_getD_ofFn
import Theorems.Thm_Printed_asked_mem_close
import Theorems.Thm_Printed_asked_W_close
import Theorems.Thm_P2M_Printed_asked___close_e2c625851c76
import Theorems.Thm_Printed_asked_f_close
import Theorems.Thm_Printed_c_le
import Theorems.Thm_Eight_Fact_getD_ofFn
import Theorems.Thm_Eight_MulOut_getD_ofFn
import Theorems.Thm_Eight_SecNetworks_Net_c_le
import Theorems.Thm_Eight_SecNetworks_size_fin
import Theorems.Thm_Eight_SecNetworks_size_ite_le
import Theorems.Thm_Eight_SecNetworks_size_word
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_NetE_getD_ofFn
import Theorems.Thm_Groundwork_Prog_NetE_size_word
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_size_fin
import Theorems.Thm_Groundwork_Prog_size_word
import Theorems.Thm_Groundwork_SatNet_c_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_Stepped_ofOption_runs
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
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_Printed_size_entry
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
theorem _root_.solution {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) :
    IsNetworkP (asked.close (netOracle N)) (netInput N P B) N P B 1 (size (netInput N P B) + 2 * size g + 4 * P + B + 4) where
  is := h
  τ_pos := le_rfl
  given :=
    { P_eq := length_unary P
      len_eq := fun a => by
        change ((List.ofFn fun a : Fin g => unary (N.len a)).getD a.val []).length = _
        rw [getD_ofFn, length_unary]
      cap_eq := fun a b hab => by
        change (((List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)).getD a.val []).getD b.val []).length = _
        rw [getD_ofFn, getD_ofFn, if_neg hab, length_unary]
      mem_runs := fun a z hz => by
        rw [asked_mem_close]
        have e : netOracle N (Sum.inl (a.val, z)) = some (if z ∈ N.S a then 1 else 0) := by simp [netOracle, hz]
        have r : (Stepped.mapOut (Stepped.ofOption fun a : NetInput × WQ => netOracle N (Sum.inl a.2)) fun v : ℤ => decide (v ≠ 0)).Runs (netInput N P B, (a.val, z)) 1 _
            (decide ((if z ∈ N.S a then (1 : ℤ) else 0) ≠ 0)) := Stepped.mapOut_runs (Stepped.ofOption_runs e)
        have e2 : decide ((if z ∈ N.S a then (1 : ℤ) else 0) ≠ 0) = decide (z ∈ N.S a) := by by_cases hm : z ∈ N.S a <;> simp [hm]
        rw [e2] at r
        refine r.mono le_rfl ?_
        have h1 := Eight.SecNetworks.size_fin a
        have h2 := Eight.SecNetworks.size_word z
        have h3 := h.len_le a
        have h4 := size_ite_le (z ∈ N.S a)
        simp only [size_prod]
        omega
      W_runs := fun a z hz => by
        rw [asked_W_close]
        have e : netOracle N (Sum.inr (Sum.inl (a.val, z))) = some (N.W a z) := by simp [netOracle, hz]
        refine (Stepped.ofOption_runs (g := fun a : NetInput × WQ => netOracle N (Sum.inr (Sum.inl a.2))) (a := (netInput N P B, (a.val, z))) e).mono le_rfl ?_
        have h1 := Eight.SecNetworks.size_fin a
        have h2 := Eight.SecNetworks.size_word z
        have h3 := h.len_le a
        have h4 := size_entry (h.ii_W a z hz)
        have h5 := h.len_S a z hz
        simp only [size_prod]
        omega
      Ψ_runs := fun a b hab z hz z' hz' => by
        rw [asked_Ψ_close]
        have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have e : netOracle N (Sum.inr (Sum.inr (Sum.inl ((a.val, b.val), (z, z'))))) = some (N.Ψ a b z z') := by simp [netOracle, hv, hz, hz']
        refine (Stepped.ofOption_runs (g := fun a : NetInput × PsiQ => netOracle N (Sum.inr (Sum.inr (Sum.inl a.2)))) (a := (netInput N P B, ((a.val, b.val), (z, z')))) e).mono le_rfl ?_
        have h1 := Eight.SecNetworks.size_fin a
        have h1' := Eight.SecNetworks.size_fin b
        have h2 := Eight.SecNetworks.size_word z
        have h2' := Eight.SecNetworks.size_word z'
        have h3 := h.len_le a
        have h3' := h.len_le b
        have h4 := size_entry (h.ii_Ψ a b hab z hz z' hz')
        have h5 := h.len_S a z hz
        have h5' := h.len_S b z' hz'
        simp only [size_prod]
        omega
      f_runs := fun a b hab z hz θ hθ => by
        rw [asked_f_close]
        have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
        have e : netOracle N (Sum.inr (Sum.inr (Sum.inr ((a.val, b.val), (z, θ))))) = some (N.f a b z θ) := by simp [netOracle, hv, hz, mem_words.1 hθ]
        refine (Stepped.ofOption_runs (g := fun a : NetInput × FQ => netOracle N (Sum.inr (Sum.inr (Sum.inr a.2)))) (a := (netInput N P B, ((a.val, b.val), (z, θ)))) e).mono le_rfl ?_
        have h1 := Eight.SecNetworks.size_fin a
        have h1' := Eight.SecNetworks.size_fin b
        have h2 := Eight.SecNetworks.size_word z
        have h2' := Eight.SecNetworks.size_word θ
        have h3 := h.len_le a
        have h3' := c_le h hab
        have h4 := size_entry (h.ii_f a b hab z hz θ hθ)
        have h5 := h.len_S a z hz
        have h5' := mem_words.1 hθ
        simp only [size_prod]
        omega }
end Printed
