-- Prove2me | solution 1 for Trace.labels_swap_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:50.645217+00:00
-- url     : https://prove2.me/submissions/5bd21147-caf8-4a3a-9d47-fab13e3724e9

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open Trace
namespace Trace
theorem _root_.solution {e₁ e₂ : α} {t₁ t₂ : List α} :
    labels lbl (t₁ ++ e₁ :: e₂ :: t₂) = labels lbl (t₁ ++ e₂ :: e₁ :: t₂) ↔
    lbl e₁ = lbl e₂ := by
  change (t₁ ++ e₁ :: e₂ :: t₂).map lbl = (t₁ ++ e₂ :: e₁ :: t₂).map lbl ↔ _
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.map_cons, List.map_cons]
  constructor
  · intro h
    have := List.append_cancel_left h
    exact (List.cons.injEq _ _ _ _ |>.mp this).1
  · intro h; rw [h]
end Trace
