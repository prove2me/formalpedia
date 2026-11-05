-- Prove2me | solution 1 for QueryMachines.QueryMachine.subst_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:54:09.453909+00:00
-- url     : https://prove2.me/submissions/0118ea33-55ef-4169-a08d-b90ec51975ca

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
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
variable [HasSize C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} {O' : Q' → Option A'}
namespace QueryMachines.QueryMachine
theorem _root_.solution {c : C} {m : M.σ} {r : N.σ} {v : A} {b : β} {t T S' Sg : ℕ} {L₁ L₂ : List Q'} (h : N.Reaches O' S' v r t L₁) (hm : size c + (size m + S' + 1) ≤ Sg)
    (hT : (M.subst N).Reaches O' Sg b (c, .inl (M.resume m v)) T L₂) : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (t + 1 + T) (L₁ ++ L₂) := by
  induction h with
  | @halt r t ho hs =>
    have e : (M.subst N).step (c, .inr (m, r)) = (c, .inl (M.resume m v)) := by
      change (match N.out r with | some v => _ | none => _) = _
      rw [ho]
    have ea : (M.subst N).ask (c, .inr (m, r)) = none := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho]
    have : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (T + 1) L₂ :=
      .step rfl ea (by change size c + (size m + size r + 1) ≤ _; omega) (e ▸ hT)
    exact this.mono (by omega) le_rfl
  | @step r t L ho ha hs _ ih =>
    have e : (M.subst N).step (c, .inr (m, r)) = (c, .inr (m, N.step r)) := by
      change (match N.out r with | some v => _ | none => _) = _
      rw [ho]
    have ea : (M.subst N).ask (c, .inr (m, r)) = none := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho, ha]
    have : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (t + 1 + T + 1) (L ++ L₂) :=
      .step rfl ea (by change size c + (size m + size r + 1) ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query r t L x w ho ha hw hs _ ih =>
    have ea : (M.subst N).ask (c, .inr (m, r)) = some x := by
      change (match N.out r with | some _ => none | none => N.ask r) = _
      rw [ho, ha]
    exact .query rfl ea hw (by change size c + (size m + size r + 1) ≤ _; omega) ih
end QueryMachines.QueryMachine
