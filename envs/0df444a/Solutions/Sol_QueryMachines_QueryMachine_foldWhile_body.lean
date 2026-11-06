-- Prove2me | solution 1 for QueryMachines.QueryMachine.foldWhile_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:27.792538+00:00
-- url     : https://prove2.me/submissions/607a4233-3d4e-4d9e-81e8-581315becaa4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}
namespace QueryMachines.QueryMachine
theorem _root_.solution {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} {L L' : List Q} (h : M.Reaches O Sm b s t L) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches O S r (Stepped.foldGo M.toStepped (g c x b) (nxt x)) T L') :
    (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (t + 1 + T) (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = Stepped.foldGo M.toStepped (g c x b) (nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (T + 1) L' :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (t + 1 + T + 1) (L ++ L') :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L y v ho ha hv hs _ ih =>
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = some y := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size x + (size c + size s) + 1 ≤ _; omega) ih
end QueryMachines.QueryMachine
