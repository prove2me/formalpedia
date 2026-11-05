-- Prove2me | solution 1 for QueryMachines.stFoldWhileRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:05:11.051968+00:00
-- url     : https://prove2.me/submissions/ea8465c9-22a0-485f-a1e3-4cfe808c5005

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

variable {Q A α β γ τ : Type}

/-- Execution bounds may be weakened without changing the result or queries. -/
private theorem Reaches_mono_aux {M : QueryMachine Q A α β} {O : Q → Option A}
    {S S' own own' : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') :
    M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)

section foldWhile

variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ}
  {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}

/-- Run the body inside the loop, then continue from the resulting loop state. -/
private theorem foldWhile_body_aux {x : τ} {c r : γ} {b : β} {s : M.σ}
    {t T Sm S : ℕ} {L L' : List Q} (h : M.Reaches O Sm b s t L)
    (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches O S r
      (Stepped.foldGo M.toStepped (g c x b) (nxt x)) T L') :
    (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s))
      (t + 1 + T) (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) =
        Stepped.foldGo M.toStepped (g c x b) (nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have hrun : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s))
        (T + 1) L' :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact Reaches_mono_aux hrun (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) =
        .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have hrun : (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s))
        (t + 1 + T + 1) (L ++ L') :=
      .step rfl ea (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact Reaches_mono_aux hrun (by omega) le_rfl
  | @query s t L y v ho ha hv hs _ ih =>
    have ea : (foldWhile start nxt M g c₀).ask (.inl (x, c, s)) = some y := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size x + (size c + size s) + 1 ≤ _; omega) ih

/-- Run the loop from an arbitrary accumulator and orbit state. -/
private theorem foldWhile_reaches_aux {xs : List τ} {o : Option τ}
    (ho : Stepped.Orbit nxt o xs) (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β)
    (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x))
    (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches O (Sx + (Sc + Sm) + 1)
      (xs.foldl (fun c x => g c x (v x)) c) (Stepped.foldGo M.toStepped c o)
      (xs.map fun x => t x + 1).sum (xs.flatMap Lq) := by
  induction ho generalizing c with
  | nil =>
    have hsize := hc [] List.nil_prefix
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at hsize; omega)
  | @cons x xs _ ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, List.flatMap_cons]
    refine foldWhile_body_aux (hM x List.mem_cons_self) ?_
      (ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy))
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl))
    have h1 := hx x List.mem_cons_self
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    omega

end foldWhile

end QueryMachines.QueryMachine

theorem solution : StFoldWhileRuns :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ c₀ _ a _ ho t Lq v Sx Sc Sm hM hx hc =>
    QueryMachine.foldWhile_reaches_aux ho t Lq v Sx Sc Sm (c₀ a) hM hx hc
