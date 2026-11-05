-- Prove2me | solution 1 for PaddedDescent.F.Mark.placeM_eq_placeAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:36.931905+00:00
-- url     : https://prove2.me/submissions/e481aa1c-ebfa-46b6-8eca-5de0db38c3f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (C : Cl) : ∀ {Ls : List Fml}, Ls ≠ [] → ∀ test : ℕ → Bool,
    (∀ i, i + 1 < Ls.length → (test i = true ↔ dropC n w C (Ls.getD i []) (Ls.drop (i + 1)))) →
    placeM n w C Ls = placeAt Ls C (((List.range (Ls.length - 1)).find? test).getD (Ls.length - 1))
  | [], h, _, _ => absurd rfl h
  | [Λ], _, _, _ => by simp [placeM, placeAt]
  | Λ :: L :: rest, _, test, ht => by
    have e : (Λ :: L :: rest).length - 1 = ((L :: rest).length - 1) + 1 := by simp
    rw [e, List.range_succ_eq_map, List.find?_cons, placeM]
    have h0 := ht 0 (by simp)
    simp only [List.getD_cons_zero, Nat.zero_add, List.drop_succ_cons, List.drop_zero] at h0
    by_cases hd : dropC n w C Λ (L :: rest)
    · rw [if_pos hd, h0.2 hd]
      simp [placeAt]
    · have hf : test 0 = false := by
        cases ht0 : test 0
        · rfl
        · exact absurd (h0.1 ht0) hd
      rw [if_neg hd, hf]
      have ih := solution (n := n) (w := w) C (List.cons_ne_nil L rest) (fun i => test (i + 1)) (fun i hi => by
        have := ht (i + 1) (by simpa using hi)
        simpa using this)
      rw [ih, List.find?_map]
      cases hfind : (List.range ((L :: rest).length - 1)).find? (test ∘ Nat.succ) with
      | none =>
        have : (List.range ((L :: rest).length - 1)).find? (fun i => test (i + 1)) = none := hfind
        rw [this]
        simp [placeAt]
      | some j =>
        have : (List.range ((L :: rest).length - 1)).find? (fun i => test (i + 1)) = some j := hfind
        rw [this]
        simp [placeAt]
end PaddedDescent.F.Mark
