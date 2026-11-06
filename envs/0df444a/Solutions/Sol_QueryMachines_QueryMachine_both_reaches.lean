-- Prove2me | solution 1 for QueryMachines.QueryMachine.both_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:52.033197+00:00
-- url     : https://prove2.me/submissions/cd0d4da4-bc7b-4ce8-83f6-542ec96521bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_both_reaches_inr
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_both_reaches_inr
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O a t' L' S' c) : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t') (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (both M N).step (.inl (a, s)) = .inr (b, N.init a) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t' + 1) L' :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ (both_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (both M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t' + 1) (L ++ L') :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L x v ho ha hv hs _ ih =>
    have ea : (both M N).ask (.inl (a, s)) = some x := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size a + size s + 1 ≤ _; omega) ih
end QueryMachines.QueryMachine
