-- Prove2me | solution 1 for QueryMachines.stBindRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:29:35.21922+00:00
-- url     : https://prove2.me/submissions/1f9258de-1299-475b-ba67-64ba07c1242d

import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic

set_option autoImplicit false

section

open QueryMachines
open Groundwork Finset QueryMachine

namespace QueryMachines.QueryMachine

variable {Q A α β γ : Type}

/-- Bounds on own steps and state sizes can be raised without changing the query list. -/
theorem Reaches.mono {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ}
    {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (ho : own ≤ own') (hS : S ≤ S') :
    M.Reaches O S' b s own' L := by
  induction h generalizing own' with
  | halt h1 h2 => exact .halt h1 (h2.trans hS)
  | step h1 h2 h3 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, own' = k + 1 := ⟨own' - 1, by omega⟩
    exact .step h1 h2 (h3.trans hS) (ih (by omega))
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 (h4.trans hS) (ih ho)

/-- The second machine of `bind`, run inside. -/
theorem bind_reaches_inr [HasSize α] {M : QueryMachine Q A α β}
    {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {S t : ℕ} {L : List Q}
    {c : γ} {s : N.σ} (h : N.Reaches O S c s t L) :
    (bind M N).Reaches O (S + 1) c (.inr s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

/-- `bind`, from a state of the first machine. -/
theorem bind_reaches [HasSize α] {M : QueryMachine Q A α β}
    {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {a : α}
    {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O (a, b) t' L' S' c) :
    (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s))
      (t + 1 + t') (L ++ L') := by
  induction h with
  | @halt s t ho hs =>
    have e : (bind M N).step (.inl (a, s)) = .inr (N.init (a, b)) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (bind M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho]
    have : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s)) (t' + 1) L' :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (bind_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t L ho ha hs _ ih =>
    have e : (bind M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have ea : (bind M N).ask (.inl (a, s)) = none := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    have : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s))
        (t + 1 + t' + 1) (L ++ L') :=
      .step rfl ea (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
  | @query s t L x v ho ha hv hs _ ih =>
    have ea : (bind M N).ask (.inl (a, s)) = some x := by
      change (match M.out s with | some _ => none | none => M.ask s) = _
      rw [ho, ha]
    exact .query rfl ea hv (by change size a + size s + 1 ≤ _; omega) ih

end QueryMachines.QueryMachine

theorem solution : StBindRuns :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h h' =>
    QueryMachines.QueryMachine.bind_reaches h h'

end
