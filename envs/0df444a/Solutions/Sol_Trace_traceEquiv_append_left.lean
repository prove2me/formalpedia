-- Prove2me | solution 1 for Trace.traceEquiv_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:01.031613+00:00
-- url     : https://prove2.me/submissions/38b23b5c-2d2b-4004-a28a-25e54f29259f

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
    (t ++ t₁) ≈ₜ (t ++ t₂) := by
  induction h generalizing t with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    calc (t ++ (t₁' ++ e₂ :: e₁ :: t₂'))
        = ((t ++ t₁') ++ e₂ :: e₁ :: t₂') := by simp
      _ ≈ₜ ((t ++ t₁') ++ e₁ :: e₂ :: t₂') := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t ++ (t₁' ++ e₁ :: e₂ :: t₂')) := by simp
      _ ≈ₜ (t ++ t₃') := ih t
end Trace
