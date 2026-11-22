-- Prove2me | solution 1 for Trace.traceEquiv_append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:07.082851+00:00
-- url     : https://prove2.me/submissions/ae329f6e-98bf-462b-b674-57f7f1857113

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
theorem _root_.solution {t₁ t₂ : List α} (h : t₁ ≈ₜ t₂) (t : List α) :
    (t₁ ++ t) ≈ₜ (t₂ ++ t) := by
  induction h with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    calc (t₁' ++ e₂ :: e₁ :: t₂' ++ t)
        = (t₁' ++ e₂ :: e₁ :: (t₂' ++ t)) := by simp
      _ ≈ₜ (t₁' ++ e₁ :: e₂ :: (t₂' ++ t)) := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t₁' ++ e₁ :: e₂ :: t₂' ++ t) := by simp
      _ ≈ₜ (t₃' ++ t) := ih
end Trace
