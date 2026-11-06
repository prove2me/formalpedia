-- Prove2me | solution 1 for SizeCircuit.addGood_addStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:04.46052+00:00
-- url     : https://prove2.me/submissions/d4744694-228d-4a67-a66d-3665670fdc88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_SizeCircuit_addStep_three
import Theorems.Thm_SizeCircuit_addStep_two
import Theorems.Thm_SizeCircuit_addStep_one
import Theorems.Thm_SizeCircuit_wfa_fullAdder
import Theorems.Thm_SizeCircuit_wfa_halfAdder
import Theorems.Thm_SizeCircuit_length_fullAdder
import Theorems.Thm_SizeCircuit_length_halfAdder
import Theorems.Thm_CircuitLowerBound_Blocks_wfa_append
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {n : ℕ} {st : AddState} (h : AddGood n st) : AddGood n (addStep n st) := by
  obtain ⟨cur, nxt, dig, K⟩ := st
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  rcases cur with _ | ⟨a, _ | ⟨u, _ | ⟨w, r⟩⟩⟩
  · exact ⟨h1, h2, h3, h4, h5⟩
  · rw [addStep_one]
    refine ⟨h2, fun x hx => absurd hx List.not_mem_nil, fun x hx => ?_, h4, fun _ => rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact h3 x hx
    · exact h1 x hx
  · rw [addStep_two]
    have hl : (K ++ halfAdder a u).length = K.length + 2 := by rw [List.length_append, length_halfAdder]
    have ha := h1 a (by simp)
    have hu := h1 u (by simp)
    refine ⟨fun x hx => ?_, fun x hx => absurd hx List.not_mem_nil, fun x hx => ?_, (wfa_append n K _).2 ⟨h4, wfa_halfAdder ha hu⟩,
      fun h => absurd h (List.cons_ne_nil _ _)⟩
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h2 x hx
        omega
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_append.1 hx with hx | hx
      · have := h3 x hx
        omega
      · rw [List.mem_singleton.1 hx]
        omega
  · rw [addStep_three]
    have hl : (K ++ fullAdder (n + K.length) a u w).length = K.length + 5 := by rw [List.length_append, length_fullAdder]
    have ha := h1 a (by simp)
    have hu := h1 u (by simp)
    have hw := h1 w (by simp)
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, (wfa_append n K _).2 ⟨h4, wfa_fullAdder ha hu hw⟩,
      fun h => absurd h (List.cons_ne_nil _ _)⟩
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h1 x (by simp [hx])
        omega
    · dsimp only at hx ⊢
      rw [hl]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h2 x hx
        omega
    · dsimp only at hx ⊢
      rw [hl]
      have := h3 x hx
      omega
end SizeCircuit
