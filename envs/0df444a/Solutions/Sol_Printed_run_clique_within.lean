-- Prove2me | solution 1 for Printed.run_clique_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:17.587532+00:00
-- url     : https://prove2.me/submissions/2f04368f-504f-4987-ad31-c0e340e375e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
import Theorems.Thm_Printed_subst_within_of
import Theorems.Thm_Printed_mapIn_within
import Theorems.Thm_Printed_clique_groupTables
import Theorems.Thm_Eight_ViaGrouping_Y_le_of_good
import Theorems.Thm_Eight_ViaGrouping_lamP_eq
import Theorems.Thm_Groundwork_Colouring_one_le_beta
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
import Theorems.Thm_Printed_asked_isNetworkP
import Theorems.Thm_Printed_length_unary
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
theorem _root_.solution (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc c₁ : ℕ} (hK0 : 0 < K) (hg : 0 < g) (hM : AchievedBy M Cc K e)
    {N : Net g} {P B τ x : ℕ} (hN : N.Is P B) (hgood : Good N.c P (Paper.grouping hK0 x))
    (hE : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * Paper.groupedLength K g N.U P),
      (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K (Paper.groupedLength K g N.U P) (γ.val, Θ)) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (c₁ * (P + B) ^ c₁)
        ((Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ) ∧
      |(Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x (Paper.groupedLength K g N.U P)).W γ Θ| < 2 ^ bitsOut K g P B) :
    ∃ TM : ℕ, (QueryMachine.mapIn (fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))))
        (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked)))).Within (netOracle N) (fun _ => τ) (netInput N P B, x)
          (TM * (c₁ * 2 ^ (P * (2 * g / K)) * τ + 2))
          (size (netInput N P B, x) + Cc * (bitsOut K g P B + Paper.groupedLength K g N.U P) ^ Cc + c₁ * (P + B) ^ c₁ + 1) N.value ∧
      (TM : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g N.U P : ℝ)) * ((bitsOut K g P B : ℝ) + (Paper.groupedLength K g N.U P : ℝ)) ^ Cc := by
  have hnet := asked_isNetworkP N hN
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Paper.groupedLength K g N.U P := ⟨_, rfl⟩
  rw [← hL] at hE ⊢
  have hlam : lamP K g asked.under (netInput N P B, x) = L := (lamP_eq hnet x).trans hL.symm
  have hL1 : 1 ≤ L := hL ▸ Colouring.one_le_beta _ _ _ _
  have hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L := fun γ γ' hne => hL ▸ Y_le_of_good hK0 hgood hne
  have hB1 : 1 ≤ bitsOut K g P B := by
    have : 1 ≤ g ^ 2 * B := Nat.mul_pos (pow_pos hg 2) hN.B_pos
    exact this.trans (Nat.le_add_left _ _)
  obtain ⟨TM, hrun, hTM⟩ := hM L (bitsOut K g P B) (groupTables N P B hK0 x L) hL1 hB1 fun w hw z hz => by
    unfold groupTables
    rw [dif_pos hw]
    exact (hE ⟨w, hw⟩ z hz).2
  rw [clique_groupTables, hV NetInput g K hK0 _ _ N P B 1 _ hnet x L hY] at hrun
  refine ⟨TM, mapIn_within ?_, hTM⟩
  change (M.subst _).Within _ _ ((netInput N P B, x), (unary (lamP K g asked.under (netInput N P B, x)), unary (bitsOut K g (unary P).length (unary B).length))) _ _ _
  rw [hlam, length_unary, length_unary]
  refine subst_within_of hSub M _ (tables K L (groupTables N P B hK0 x L)) (netOracle N) (fun _ => τ) (netInput N P B, x) _ TM _ _ _ _ hrun fun q v hq => mapIn_within ?_
  simp only [tables] at hq
  split_ifs at hq with hc
  obtain rfl := Option.some.inj hq
  change (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K (lamP K g asked.under (netInput N P B, x)) q) _ _ _
  rw [hlam]
  unfold groupTables
  rw [dif_pos hc.1]
  exact (hE ⟨q.1, hc.1⟩ q.2 (mem_words.2 hc.2)).1
end Printed
