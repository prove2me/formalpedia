-- Prove2me | solution 1 for Printed.groupingMachine_computes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:52:02.707531+00:00
-- url     : https://prove2.me/submissions/fb5a59b0-2528-4faa-af26-ae936fc6be01

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
import Theorems.Thm_Printed_optBind_within
import Theorems.Thm_Printed_bitsOut_le_Bp
import Theorems.Thm_Printed_poly_le_three
import Theorems.Thm_Printed_run_clique_within
import Theorems.Thm_Eight_SecNetworks_L_le
import Theorems.Thm_Eight_SecNetworks_U_le
import Theorems.Thm_Eight_ViaGrouping_Cost_base_le
import Theorems.Thm_Eight_ViaGrouping_Cost_bound_follows
import Theorems.Thm_Eight_ViaGrouping_Y_le_of_good
import Theorems.Thm_Eight_ViaGrouping_exponent_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_size_netInput_le
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
import Theorems.Thm_SingleBitPieces_exponent_eq
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
theorem _root_.solution (hStops : Exits.StSearchStops) (hE : StEntryCost) (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc : ℕ} (hK0 : 0 < K) (hg : 0 < g) (h0 : 0 ≤ e)
    (hM : AchievedBy M Cc K e)
    (hS : ∀ (N : Net g) (P B : ℕ), N.Is P B → ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g (asked.close (netOracle N)) (netInput N P B, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) hK0 x)) :
    ∃ C₁ : ℕ, ComputesNetworks (groupingMachine K g M) C₁ g K e := by
  -- the constants
  obtain ⟨c₁, hc₁⟩ := hE K g
  obtain ⟨A1, hA1⟩ := Cost.bound_follows (K := K) (g := g) Cc (c₁ + 2) (2 * K ^ g + 1) hK0 hg h0
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * g ^ 2 + 6 * g + 6 := ⟨_, rfl⟩
  obtain ⟨sx, hsx⟩ : ∃ sx, sx = size (K ^ g) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * g + g ^ 2 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = (5 * D + 5 * sx + 13) + Cc * G ^ Cc + c₁ + Cc := ⟨_, rfl⟩
  refine ⟨max A1 A2, fun N P B τ hN hτ => ?_⟩
  have hP := hN.P_pos
  have hU := U_le hN
  -- fix the first good grouping, number x
  obtain ⟨x, hxlt, hfind, hgood⟩ := hS N P B hN
  have hsearch : (Exits.search K g asked.under).Runs (netInput N P B) (2 * (x + 1)) (4 * (size (netInput N P B) + size (K ^ g)) + 10) (some x) :=
    hStops K g NetInput (asked.close (netOracle N)) (netInput N P B) x hfind
  -- the cost of one entry; the run of the algorithm for (K, e)
  have hLle : Paper.groupedLength K g N.U P ≤ 2 * (g * P) := L_le hK0 hg hP hU
  obtain ⟨TM, hrun, hTM⟩ := run_clique_within hV hSub hK0 hg hM hN hgood
    (hc₁ hK0 hg N P B τ hN hτ x hxlt _ hLle hgood.G1 fun γ γ' hne => Y_le_of_good hK0 hgood hne)
  have hall := optBind_within (dflt := zeroOf) hsearch hrun
  obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ (P * (2 * g / K)) := ⟨_, rfl⟩
  rw [← hn] at hall
  have hn1 : 1 ≤ n := hn ▸ Nat.one_le_two_pow
  have hBB := bitsOut_le_Bp hK0 g P B
  refine ⟨2 * (x + 1) + 1 + TM * (c₁ * n * τ + 2), hall.mono le_rfl ?_, ?_⟩
  · -- the sizes of the states
    have hs := size_netInput_le N hN
    rw [← hD] at hs
    have hbase := Cost.base_le N.U P B hK0 hg hP hU
    rw [← hG] at hbase
    obtain ⟨X, hX⟩ : ∃ X, X = P + B := ⟨_, rfl⟩
    rw [← hX] at hs hbase ⊢
    have hX1 : 1 ≤ X := by omega
    have hx : size x ≤ sx := by
      rw [hsx]
      simp only [size_nat]
      exact Nat.succ_le_succ (Nat.size_le_size hxlt.le)
    have a2 : Cc * (bitsOut K g P B + Paper.groupedLength K g N.U P) ^ Cc ≤ Cc * G ^ Cc * X ^ Cc := by
      rw [Nat.mul_assoc, ← Nat.mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have a3 : (5 * D + 5 * sx + 13) * X = 5 * (D * X) + (5 * sx + 13) * X := by ring
    have a4 : (5 * sx + 13) * 1 ≤ (5 * sx + 13) * X := Nat.mul_le_mul_left _ hX1
    have a5 := poly_le_three (D := 5 * D + 5 * sx + 13) (M := Cc * G ^ Cc) (M' := c₁) (k := Cc) (k' := c₁) (c := A2) hX1 (by omega) (by omega) (by omega) (by omega)
    have a6 : A2 * X ^ A2 ≤ max A1 A2 * X ^ max A1 A2 := Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hX1 (le_max_right _ _))
    have e : size (netInput N P B, x) = size (netInput N P B) + size x := rfl
    rw [e, ← hsx]
    generalize size (netInput N P B) = sc at hs ⊢
    omega
  · -- the bound follows
    have hTE : ((TM * ((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ) : ℕ) : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) *
        ((Cost.Bp K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ Cc * (((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      refine mul_le_mul_of_nonneg_right (hTM.trans ?_) (Nat.cast_nonneg _)
      have hBB' : (bitsOut K g P B : ℝ) ≤ (Cost.Bp K g P B : ℝ) := by exact_mod_cast hBB
      gcongr
    have hT : 2 * (x + 1) + 1 + TM * (c₁ * n * τ + 2) ≤ 2 * K ^ g + 1 + TM * ((c₁ + 2) * 2 ^ (P * (2 * g / K)) * τ) := by
      rw [← hn]
      have b1 : c₁ * n * τ + 2 ≤ (c₁ + 2) * n * τ := by
        have : (c₁ + 2) * n * τ = c₁ * n * τ + 2 * (n * τ) := by ring
        have : 1 ≤ n * τ := Nat.mul_pos hn1 hτ
        omega
      have b2 := Nat.mul_le_mul_left TM b1
      omega
    have hfin := hA1 P B τ N.U _ _ hP hτ hU hTE hT
    rw [exponent_eq] at hfin
    refine hfin.trans ?_
    have hY : (1 : ℝ) ≤ (P : ℝ) + B := by exact_mod_cast (by omega : 1 ≤ P + B)
    have hAm : (A1 : ℝ) ≤ ((max A1 A2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hYp : ((P : ℝ) + B) ^ A1 ≤ ((P : ℝ) + B) ^ (max A1 A2) := pow_le_pow_right₀ hY (le_max_left _ _)
    gcongr
end Printed
