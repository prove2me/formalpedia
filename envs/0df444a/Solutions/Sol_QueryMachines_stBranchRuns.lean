-- Prove2me | solution 1 for QueryMachines.stBranchRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:57:21.049134+00:00
-- url     : https://prove2.me/submissions/cd224524-a5de-496d-9c6f-9ccbd3d268f5

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

private theorem branch_reaches_inl_aux {Q A α α₁ α₂ β : Type}
    {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β}
    {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₁.σ}
    (h : M₁.Reaches O S b s t L) :
    (branch sel M₁ M₂).Reaches O (S + 1) b (.inl s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

private theorem branch_reaches_inr_aux {Q A α α₁ α₂ β : Type}
    {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β}
    {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₂.σ}
    (h : M₂.Reaches O S b s t L) :
    (branch sel M₁ M₂).Reaches O (S + 1) b (.inr s) t L := by
  induction h with
  | halt ho hs => exact .halt ho (Nat.succ_le_succ hs)
  | step ho ha hs _ ih => exact .step ho ha (Nat.succ_le_succ hs) ih
  | query ho ha hv hs _ ih => exact .query ho ha hv (Nat.succ_le_succ hs) ih

end QueryMachines.QueryMachine

theorem solution : StBranchRuns := fun _ _ _ _ _ _ sel M₁ M₂ _ a _ _ _ _ =>
  ⟨fun x hs h => by
    have e : (branch sel M₁ M₂).init a = .inl (M₁.init x) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inl_aux h,
   fun y hs h => by
    have e : (branch sel M₁ M₂).init a = .inr (M₂.init y) := by
      change (match sel a with | .inl x => _ | .inr y => _) = _
      rw [hs]
    unfold Runs
    rw [e]
    exact branch_reaches_inr_aux h⟩
