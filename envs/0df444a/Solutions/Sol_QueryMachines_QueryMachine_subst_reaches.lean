-- Prove2me | solution 1 for QueryMachines.QueryMachine.subst_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:55:25.053833+00:00
-- url     : https://prove2.me/submissions/b21140b2-bfee-43ac-8cb8-04f79425e37e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_subst_inner
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
theorem _root_.solution {O : Q → Option A} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} {L' : Q → List Q'} (h : M.Reaches O S b s own L)
    (hN : ∀ x ∈ L, ∀ v, O x = some v → N.Runs O' (c, x) (t x) (L' x) S' v) :
    (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (own + (L.map fun x => t x + 2).sum) (L.flatMap L') := by
  induction h with
  | halt ho hs => exact .halt ho (by change size c + (size _ + 1) ≤ _; omega)
  | @step s own L ho ha hs _ ih =>
    have e : (M.subst N).step (c, .inl s) = (c, .inl (M.step s)) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have : (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (own + (L.map fun x => t x + 2).sum + 1) (L.flatMap L') :=
      .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ ih hN)
    exact this.mono (by omega) le_rfl
  | @query s own L x v ho ha hv hs _ ih =>
    have e : (M.subst N).step (c, .inl s) = (c, .inr (s, N.init (c, x))) := by
      change (match M.ask s with | some x => _ | none => _) = _
      rw [ha]
    have h1 := subst_inner (M := M) (c := c) (m := s) (Sg := size c + S + S' + 1) (hN x List.mem_cons_self v hv) (by omega)
      (ih fun y hy => hN y (List.mem_cons_of_mem _ hy))
    have : (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (t x + 1 + (own + (L.map fun x => t x + 2).sum) + 1) (L' x ++ L.flatMap L') :=
      .step ho rfl (by change size c + (size s + 1) ≤ _; omega) (e ▸ h1)
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact this.mono (by omega) le_rfl
end QueryMachines.QueryMachine
