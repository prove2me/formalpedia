-- Prove2me | solution 1 for QueryMachines.stFoldRangeRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:48:38.560168+00:00
-- url     : https://prove2.me/submissions/9957b4f9-3f34-4610-a471-161f654dcdfe

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

open Groundwork Finset

variable {Q Q' A α α₁ α₂ β γ τ : Type}

/-- The bounds on steps and sizes may be raised without changing the queries. -/
theorem Reaches.mono {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') : M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)

section foldWhile

variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}

/-- The body, run inside the loop. -/
theorem foldWhile_body_aux {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} {L L' : List Q} (h : M.Reaches O Sm b s t L) (hS : size x + (size c + Sm) + 1 ≤ S)
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

/-- The loop, from the state with accumulator c and next point o. -/
theorem foldWhile_reaches_aux {xs : List τ} {o : Option τ} (ho : Stepped.Orbit nxt o xs) (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx) (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches O (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c) (Stepped.foldGo M.toStepped c o) (xs.map fun x => t x + 1).sum (xs.flatMap Lq) := by
  induction ho generalizing c with
  | nil =>
    have := hc [] (List.nil_prefix)
    exact .halt rfl (by change size c + 1 ≤ _; simp only [List.foldl_nil] at this; omega)
  | @cons x xs _ ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, List.flatMap_cons]
    refine foldWhile_body_aux (hM x List.mem_cons_self) ?_
      (ih (g c x (v x)) (fun y hy => hM y (List.mem_cons_of_mem _ hy)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        fun l hl => by simpa using hc (x :: l) ((List.prefix_cons_inj x).2 hl))
    have h1 := hx x List.mem_cons_self
    have h2 := hc [] List.nil_prefix
    simp only [List.foldl_nil] at h2
    omega

end foldWhile

/-- The points of the loop over y < N a. -/
theorem orbit_range_aux (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Stepped.Orbit (Stepped.rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by
  induction k generalizing y with
  | zero => rw [if_neg (by omega)]; exact .nil
  | succ k ih =>
    rw [if_pos (by omega), List.range'_succ, List.map_cons]
    exact .cons (ih (y + 1) (by omega))

/-- A sum over a list of numbers 0, …, n − 1 as a sum over a range. -/
theorem sum_map_range_aux (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The loop over a range. -/
theorem foldRange_runs_aux [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {a : α}
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have ho := orbit_range_aux N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have := foldWhile_reaches_aux (start := Stepped.rangeStart N) (M := M) (g := Stepped.rangeG g) (c₀ := c₀) (O := O) ho (fun x => t x.2) (fun x => Lq x.2) (fun x => v x.2)
    (size a + size (N a)) Sc Sm (c₀ a)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size (List.mem_range.1 hy).le
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      exact hc _ (min_le_right _ _))
  rw [List.map_map, List.foldl_map, List.flatMap_map] at this
  rw [← sum_map_range_aux]
  exact this

end QueryMachines.QueryMachine

theorem solution : StFoldRangeRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ _ t Lq v Sc Sm hM hc =>
  QueryMachines.QueryMachine.foldRange_runs_aux t Lq v Sc Sm hM hc
