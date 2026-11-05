-- Prove2me | solution 1 for QueryMachines.QueryMachine.subst_reaches_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:03:21.082383+00:00
-- url     : https://prove2.me/submissions/44d2ff47-8c58-43ee-a233-28b4ce9dbaff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_subst_inner
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
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
variable [HasSize C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} {O' : Q' → Option A'}
namespace QueryMachines.QueryMachine
theorem _root_.solution {O : Q → Option A} {w' : Q' → ℕ} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} (h : M.Reaches O S b s own L)
    (hN : ∀ x v, O x = some v → N.Within O' w' (c, x) (t x) S' v) :
    ∃ (own₂ : ℕ) (L₂ : List Q'), (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) own₂ L₂ ∧ own₂ + (L₂.map w').sum ≤ own + (L.map fun x => t x + 2).sum := by
  induction h with
  | halt ho hs => exact ⟨0, [], .halt ho (by change size c + (size _ + 1) ≤ _; omega), by simp⟩
  | @step s own L ho ha hs _ ih =>
    obtain ⟨o₂, L₂, hr, hle⟩ := ih
    have e : (M.subst N).step (c, .inl s) = (c, .inl (M.step s)) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    exact ⟨o₂ + 1, L₂, .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ hr), by omega⟩
  | @query s own L x v ho ha hv hs _ ih =>
    obtain ⟨o₂, L₂, hr, hle⟩ := ih
    obtain ⟨o₁, L₁, hr₁, hle₁⟩ := hN x v hv
    have e : (M.subst N).step (c, .inl s) = (c, .inr (s, N.init (c, x))) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have h1 := subst_inner (M := M) (c := c) (m := s) (Sg := size c + S + S' + 1) hr₁ (by omega) hr
    exact ⟨o₁ + 1 + o₂ + 1, L₁ ++ L₂, .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ h1), by
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]; omega⟩
end QueryMachines.QueryMachine
