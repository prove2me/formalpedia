-- Prove2me | solution 1 for Wrap.pad4KeepsSatAndMeetsSideConditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:12:03.570644+00:00
-- url     : https://prove2.me/submissions/d19e0e13-b8f1-40ff-a273-681d43b71bcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Wrap_castLit_injective
import Theorems.Thm_Wrap_mem_pad4
import Theorems.Thm_Wrap_numOcc_le
import Theorems.Thm_Wrap_occurs_pad4
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.map
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
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution : Pad4KeepsSatAndMeetsSideConditions := by
  intro n φ hφ
  obtain ⟨h3, hnd⟩ := hφ
  refine ⟨⟨?_, ?_⟩, ?_, ?_, numOcc_le _, ?_, ?_⟩
  · intro D hD
    rcases mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · simpa using h3 C hC
    · simp
  · unfold pad4
    refine List.Nodup.append (hnd.map (List.map_injective_iff.2 (castLit_injective n))) ((List.nodup_finRange 4).map ?_) ?_
    · intro a b h
      simpa using h
    · intro D h1 h2
      obtain ⟨C, -, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j, -, h⟩ := List.mem_map.1 h2
      match C, h with
      | [], h => simp at h
      | [l], h =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at h
        have := congrArg Fin.val h.1
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := l.1.2
        omega
      | _ :: _ :: _, h => simp at h
  · simp [pad4]
  · have h := Nat.card_le_card_of_injective (fun j : Fin 4 => (⟨Fin.natAdd n j, occurs_pad4 φ j⟩ : {i : Fin (n + 4) // MainTheoremForms.Occurs (pad4 φ) i})) (by
      intro a b h
      simpa using h)
    simpa [MainTheoremForms.numOcc] using h
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a (Fin.castAdd 4 i), fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := ha _ (mem_pad4.2 (Or.inl ⟨C, hC, rfl⟩))
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨l', hl', h⟩
  · rintro ⟨a, ha⟩
    refine ⟨Fin.addCases a fun _ => true, fun D hD => ?_⟩
    rcases mem_pad4.1 hD with ⟨C, hC, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨l, hl, h⟩ := ha C hC
      exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, by simpa using h⟩
    · exact ⟨_, List.mem_singleton.2 rfl, by simp⟩
end Wrap
