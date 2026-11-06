-- Prove2me | solution 1 for SizeCircuit.stGammaCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:16:41.944546+00:00
-- url     : https://prove2.me/submissions/55e438f0-f59f-4027-92d3-e41ed4af8f24

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_SizeCircuit_stGamma
import Theorems.Thm_SizeCircuit_holds_restrict
import Theorems.Thm_CountKSat_StepCount_holds_append
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filter
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
import Theorems.Thm_SizeCircuit_holds_append
attribute [local fun_prop] Groundwork.PolyT.filter
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
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution : StGammaCount := by
  intro gates a hT n s ψ hψ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e1 : numVars gates 0 s = 0 := if_pos rfl
    have e2 : gamma gates 0 s = if s = 0 then [] else [[]] := if_pos rfl
    have hcard : ∀ x : Fin 0 → Bool, (Finset.univ.filter fun i => x i = true).card = 0 := fun x => by simp
    rw [e1, e2]
    unfold cntN cntS
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    rw [hcard x]
    by_cases hs : s = 0
    · rw [if_pos hs, List.append_nil]
      exact ⟨fun h => ⟨h, hs.symm⟩, fun h => h.1⟩
    · rw [if_neg hs]
      constructor
      · intro h
        obtain ⟨l, hl, -⟩ := h [] (by simp)
        exact absurd hl List.not_mem_nil
      · rintro ⟨-, h⟩
        exact absurd h.symm hs
  · have e1 : numVars gates n s = n + (gates n s).length := if_neg (by omega)
    have e2 : gamma gates n s = formulaOf n (gates n s) := if_neg (by omega)
    obtain ⟨-, -, -, hx⟩ := stGamma gates a hT n s hn
    rw [e1, e2]
    unfold cntN cntS
    have hsize : ∀ b : Fin (n + (gates n s).length) → Bool, Holds (ext b) (formulaOf n (gates n s)) →
        (Finset.univ.filter fun i => b (Fin.castAdd (gates n s).length i) = true).card = s := by
      intro b hb
      by_contra hne
      exact (hx fun i => b (Fin.castAdd (gates n s).length i)).2 hne ⟨b, fun _ => rfl, hb⟩
    refine Finset.card_bij (fun b _ => fun i => b (Fin.castAdd (gates n s).length i)) ?_ ?_ ?_
    · intro b hb
      obtain ⟨h1, h2⟩ := (holds_append _ _ _).1 (Finset.mem_filter.1 hb).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (holds_restrict b _ (fun _ => rfl) hψ).1 h1, hsize b h2⟩
    · intro b hb b' hb' e
      have h2 := ((holds_append _ _ _).1 (Finset.mem_filter.1 hb).2).2
      have h2' := ((holds_append _ _ _).1 (Finset.mem_filter.1 hb').2).2
      obtain ⟨b0, -, hu⟩ := (hx fun i => b (Fin.castAdd (gates n s).length i)).1 (hsize b h2)
      exact (hu b ⟨fun _ => rfl, h2⟩).trans (hu b' ⟨fun i => (congrFun e i).symm, h2'⟩).symm
    · intro x hxm
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hxm
      obtain ⟨b, ⟨hb, hH⟩, -⟩ := (hx x).1 h2
      exact ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, (holds_append _ _ _).2 ⟨(holds_restrict b x hb hψ).2 h1, hH⟩⟩, funext hb⟩
end SizeCircuit
