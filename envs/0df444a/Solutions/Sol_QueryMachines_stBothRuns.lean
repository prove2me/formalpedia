-- Prove2me | solution 1 for QueryMachines.stBothRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:24:46.855416+00:00
-- url     : https://prove2.me/submissions/9a233911-2ed0-42f5-ac1c-3fc38a6da900

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine

namespace QueryMachines.QueryMachine

/-- Bounds on own steps and state sizes can be raised without changing a run. -/
theorem Reaches.mono {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A}
    {S S' own own' : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') :
    M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)

/-- A run of the second machine, embedded in `both`. -/
theorem both_reaches_inr {Q A α β γ : Type} [HasSize α] [HasSize β]
    {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A}
    {S t : ℕ} {L : List Q} {b : β} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) :
    (both M N).Reaches O (size b + S + 1) (b, c) (.inr (b, s)) t L := by
  induction h with
  | @halt s t ho hs =>
    exact .halt (by change (N.out s).map _ = _; rw [ho]; rfl)
      (by change size b + size s + 1 ≤ _; omega)
  | @step s t L ho ha hs _ ih =>
    exact .step (by change (N.out s).map _ = _; rw [ho]; rfl) ha
      (by change size b + size s + 1 ≤ _; omega) ih
  | @query s t L x v ho ha hv hs _ ih =>
    exact .query (by change (N.out s).map _ = _; rw [ho]; rfl) ha hv
      (by change size b + size s + 1 ≤ _; omega) ih

/-- A run of `both`, obtained by following the first machine and then the second. -/
theorem both_reaches {Q A α β γ : Type} [HasSize α] [HasSize β]
    {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A}
    {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O a t' L' S' c) :
    (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c)
      (.inl (a, s)) (t + 1 + t') (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (both M N).step (.inl (a, s)) = .inr (b, N.init a) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have hr : (both M N).Reaches O (max (size a + S) (size b + S') + 1)
        (b, c) (.inl (a, s)) (t' + 1) L' :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (both_reaches_inr h').mono le_rfl (by omega))
    exact hr.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (both M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (both M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have hr : (both M N).Reaches O (max (size a + S) (size b + S') + 1)
        (b, c) (.inl (a, s)) (t + 1 + t' + 1) (L ++ L') :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact hr.mono (by omega) le_rfl
  | @query s t L x v ho ha hv hs _ ih =>
    have ea : (both M N).ask (.inl (a, s)) = some x := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size a + size s + 1 ≤ _; omega) ih

end QueryMachines.QueryMachine

theorem solution : StBothRuns :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' =>
    QueryMachines.QueryMachine.both_reaches h h'
